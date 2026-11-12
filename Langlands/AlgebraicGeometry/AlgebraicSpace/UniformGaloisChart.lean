import Langlands.AlgebraicGeometry.AlgebraicSpace.AffineChartFibrePower
import Langlands.AlgebraicGeometry.AlgebraicSpace.RationalPointEtaleLiftProof

/-!
# One affine chart for all rational points lifting over a fixed Galois extension

Let `X` be a separated algebraic space over a field `k`, `a : h_V → X` an étale chart from an
affine separated scheme `V`, and `K/k` a finite Galois extension with group `G`. The `G`-fold
fibre power `Y` of `a` is affine, so `Z = Y ×_k Spec K` is affine with a free diagonal action
of `G`. The quotient `M = Z/G` is a single affine scheme with an étale map to `X`. Every
`k`-point of `X` that lifts to a `K`-point of `V` is the image of a `k`-point of `M`.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Langlands.AlgebraicGeometry.Picard.DualNumberDouble (specOverMap specOverMap_left)
open Langlands.AlgebraicGeometry.PointTopology (ringTest RingPoint ringTestMap)

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace UniformGaloisChart

variable {k : Type u} [Field k]

/-- **One chart for a Galois extension.** For a separated space `X`, an affine étale chart
`a : h_V → X` and a finite Galois extension `K/k`, there is one affine scheme `M` with an étale
map to `X` such that every `k`-point of `X` lifting to a `K`-point of `V` comes from a
Galois-invariant `K`-point of `M`. -/
theorem exists_chart (X : AlgebraicSpace (Spec (CommRingCat.of k))) (hX : IsSeparated X)
    (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {V : Over (Spec (CommRingCat.of k))} [IsAffine V.left]
    (a : (schemeYoneda _).obj V ⟶ X.presheaf) [_root_.AlgebraicGeometry.IsSeparated V.hom]
    (ha : IsEtale a) :
    ∃ (M : Over (Spec (CommRingCat.of k))) (tM : (schemeYoneda _).obj M ⟶ X.presheaf),
      IsAffine M.left ∧ IsEtale tM ∧
      ∀ (xh : (schemeYoneda (Spec (CommRingCat.of k))).obj (ringTest k k) ⟶ X.presheaf)
        (v : specOver k K ⟶ V) (π : specOver k K ⟶ ringTest k k),
        (schemeYoneda _).map v ≫ a = (schemeYoneda _).map π ≫ xh →
        ∃ w : specOver k K ⟶ M, (∀ g : K ≃ₐ[k] K, specOverMap g.toAlgHom ≫ w = w) ∧
          (schemeYoneda _).map w ≫ tM = (schemeYoneda _).map π ≫ xh := by
  obtain ⟨Y, hYsep, hYet, hYaff⟩ :=
    ChartFibrePower.exists_of_finite_affine hX ha (K ≃ₐ[k] K)
  obtain ⟨ρ, hρ⟩ : ∃ ρ : OverAction (K ≃ₐ[k] K) Y.obj, ∀ g, ρ.act g = Y.act g :=
    ⟨⟨Y.act, Y.act_one, Y.act_mul⟩, fun _ => rfl⟩
  obtain ⟨σ, hσ, hσfree⟩ : ∃ σ : OverAction (K ≃ₐ[k] K) (specOver k K),
      (∀ g, σ.act g = specOverMap g.toAlgHom) ∧ σ.IsFree :=
    ⟨OverAction.galoisAction, fun _ => rfl, OverAction.galoisAction_isFree⟩
  have hfree : (ρ.prod σ).IsFree := ρ.prod_isFree σ hσfree
  let Z := OverAction.prodOver Y.obj (specOver k K)
  have : IsAffine (specOver k K).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of K)))
  have hZaff : IsAffine Z.left :=
    inferInstanceAs (IsAffine (Limits.pullback Y.obj.hom (specOver k K).hom))
  have : _root_.AlgebraicGeometry.IsSeparated Z.hom := by
    have := hYsep
    change _root_.AlgebraicGeometry.IsSeparated
      (Limits.pullback.snd Y.obj.hom (specOver k K).hom ≫ (specOver k K).hom)
    infer_instance
  let t : (schemeYoneda _).obj Z ⟶ X.presheaf :=
    (schemeYoneda _).map OverAction.prodFst ≫ (schemeYoneda _).map (Y.pr 1) ≫ a
  have ht : IsEtale t :=
    IsEtale.comp (isEtale_map _ inferInstance) (IsEtale.comp (isEtale_map _ (hYet 1)) ha)
  have hinv : ∀ g, (schemeYoneda _).map ((ρ.prod σ).act g) ≫ t = t := by
    intro g
    simp only [t]
    rw [← Functor.map_comp_assoc, OverAction.prod_act_fst, Functor.map_comp_assoc, hρ,
      ← Functor.map_comp_assoc _ (Y.act g), Y.act_pr, Y.w (g * 1) 1]
  let U : Z.left.Opens := ⊤
  have hU : ∀ g, ((ρ.prod σ).act g).left ⁻¹ᵁ U = U := fun g => Scheme.Hom.preimage_top _
  have : IsAffine (OverAction.resOver U).left := isAffineOpen_top Z.left
  obtain ⟨M, q, tM, hM, htM, hq, hqt⟩ :=
    (ρ.prod σ).exists_quotient_chart U hU hfree X t ht hinv
  refine ⟨M, tM, hM, htM, fun xh v π hv => ?_⟩
  have hπ : ∀ g : K ≃ₐ[k] K, specOverMap g.toAlgHom ≫ π = π := fun _ =>
    GaloisChartPoint.ringTest_self_hom_ext _ _
  have hvg : ∀ g : K ≃ₐ[k] K, (schemeYoneda _).map (specOverMap g.toAlgHom ≫ v) ≫ a =
      (schemeYoneda _).map π ≫ xh := fun g => by
    rw [Functor.map_comp_assoc, hv, ← Functor.map_comp_assoc, hπ]
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : specOver k K ⟶ Y.obj,
      ∀ g, y₀ ≫ Y.pr g = specOverMap g.toAlgHom ≫ v :=
    ⟨Y.lift (fun g => specOverMap g.toAlgHom ≫ v) fun g h => by rw [hvg, hvg], Y.lift_pr _ _⟩
  obtain ⟨z, hzfst, hzsnd⟩ : ∃ z : specOver k K ⟶ Z,
      z ≫ OverAction.prodFst = y₀ ∧ z ≫ OverAction.prodSnd = 𝟙 _ :=
    ⟨OverAction.prodLift y₀ (𝟙 _), OverAction.prodLift_fst _ _, OverAction.prodLift_snd _ _⟩
  have hz : ∀ g, z ≫ (ρ.prod σ).act g = σ.act g ≫ z := by
    intro g
    apply OverAction.prod_hom_ext
    · rw [Category.assoc, OverAction.prod_act_fst, reassoc_of% hzfst, Category.assoc, hzfst,
        hρ]
      apply Y.hom_ext
      intro e
      rw [Category.assoc, Y.act_pr, hy₀, Category.assoc, hy₀, ← Category.assoc]
      simp only [← hσ, σ.mul]
    · rw [Category.assoc, OverAction.prod_act_snd, reassoc_of% hzsnd, Category.assoc, hzsnd,
        Category.comp_id]
  have hzg : ∀ g, z.left ≫ ((ρ.prod σ).act g).left = (σ.act g).left ≫ z.left := fun g =>
    congrArg CommaMorphism.left (hz g)
  -- `z` factors through the stable open `⊤`
  have hrange : Set.range z.left ⊆ Set.range (OverAction.resOverι U).left := by
    rintro _ ⟨y', rfl⟩
    exact ⟨⟨z.left y', trivial⟩, Scheme.Opens.ι_apply _ _⟩
  obtain ⟨z₁, hz₁⟩ : ∃ z₁ : (specOver k K).left ⟶ (OverAction.resOver U).left,
      z₁ ≫ (OverAction.resOverι U).left = z.left :=
    ⟨_root_.AlgebraicGeometry.IsOpenImmersion.lift (OverAction.resOverι U).left z.left hrange,
      _root_.AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ hrange⟩
  let z' : specOver k K ⟶ OverAction.resOver U := Over.homMk z₁ (by
    change z₁ ≫ (OverAction.resOverι U).left ≫ Z.hom = (specOver k K).hom
    rw [reassoc_of% hz₁, Over.w z])
  have hz' : z' ≫ OverAction.resOverι U = z := Over.OverMorphism.ext hz₁
  refine ⟨z' ≫ q, fun g => ?_, ?_⟩
  · have h₁ : (σ.act g).left ≫ z₁ = z₁ ≫ (ρ.prod σ).resAct U hU g := by
      rw [← cancel_mono (OverAction.resOverι U).left, Category.assoc, hz₁, Category.assoc,
        OverAction.resAct_ι, reassoc_of% hz₁, hzg]
    apply Over.OverMorphism.ext
    change (specOverMap g.toAlgHom).left ≫ z₁ ≫ q.left = z₁ ≫ q.left
    rw [← hσ, reassoc_of% h₁, hq]
  · rw [Functor.map_comp_assoc, hqt, ← Functor.map_comp_assoc, hz']
    simp only [t]
    rw [← Functor.map_comp_assoc, hzfst, ← Functor.map_comp_assoc, hy₀, hvg]

end UniformGaloisChart

end Langlands.AlgebraicGeometry.AlgebraicSpace
