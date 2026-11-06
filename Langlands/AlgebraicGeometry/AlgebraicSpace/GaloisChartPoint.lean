import Langlands.AlgebraicGeometry.AlgebraicSpace.SpecFieldPoints
import Langlands.AlgebraicGeometry.AlgebraicSpace.RingPoints
import Langlands.AlgebraicGeometry.AlgebraicSpace.FppfQuotientRepresentability
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationPresentation
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Galois points of étale charts over a field

Let `k` be a field and `X` an algebraic space over `Spec k`.

* Every `k`-point of `X` lifts, after the base change to a finite Galois extension `K/k`,
  to a `K`-point of an affine scheme with an étale map to `X`
  (`GaloisChartPoint.exists_galois_chart`).
* A `K`-point of an affine scheme over `Spec k` that is invariant under `Gal(K/k)` comes
  from a `k`-point (`GaloisChartPoint.exists_desc_of_galois_invariant`).
* The `k`-points of `X` inject into its `K`-points for every finite extension `K/k`
  (`GaloisChartPoint.changeRing_injective`).
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Langlands.AlgebraicGeometry.Picard.DualNumberDouble (specOverMap specOverMap_left)
open Langlands.AlgebraicGeometry.PointTopology (ringTest RingPoint ringTestMap)

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace GaloisChartPoint

variable {k : Type u} [Field k]

/-- Every finite separable extension embeds in a finite Galois extension in the same
universe: the normal closure inside a separable closure. -/
theorem exists_galois_of_separable (L : Type u) [Field L] [Algebra k L]
    [FiniteDimensional k L] [Algebra.IsSeparable k L] :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K), FiniteDimensional k K ∧ IsGalois k K ∧
      Nonempty (L →ₐ[k] K) := by
  let F := SeparableClosure k
  let ι : L →ₐ[k] F := IsSepClosed.lift
  let _ : Algebra L F := ι.toAlgebra
  have : IsScalarTower k L F := IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  exact ⟨IntermediateField.normalClosure k L F, inferInstance, inferInstance, inferInstance,
    inferInstance, ⟨(normalClosure.algHomEquiv k L F).symm ι⟩⟩

/-- The structure morphism of `Spec k` over itself is the identity. -/
theorem ringTest_self_hom : (ringTest k k).hom = 𝟙 _ := by
  change Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 _
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

/-- A morphism to `Spec k` over `Spec k` is the structure morphism of its source. -/
theorem ringTest_self_left {T : Over (Spec (CommRingCat.of k))} (f : T ⟶ ringTest k k) :
    f.left = T.hom :=
  (Category.comp_id f.left).symm.trans
    ((congrArg (f.left ≫ ·) ringTest_self_hom.symm).trans (Over.w f))

/-- `Spec k` is terminal over itself: any two morphisms to it agree. -/
theorem ringTest_self_hom_ext {T : Over (Spec (CommRingCat.of k))} (f g : T ⟶ ringTest k k) :
    f = g :=
  Over.OverMorphism.ext ((ringTest_self_left f).trans (ringTest_self_left g).symm)

/-- A nonempty scheme étale over `Spec k` has a point with values in a finite separable
extension of `k`. -/
theorem exists_separable_point (T : Over (Spec (CommRingCat.of k))) [Etale T.hom]
    [Nonempty T.left] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L), FiniteDimensional k L ∧
      Algebra.IsSeparable k L ∧ Nonempty (specOver k L ⟶ T) := by
  obtain ⟨z⟩ := ‹Nonempty T.left›
  obtain ⟨W, hW, hzW, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show z ∈ (⊤ : T.left.Opens) from trivial)
  let A := Γ(T.left, W)
  let ψ : CommRingCat.of k ⟶ A := Spec.preimage (hW.fromSpec ≫ T.hom)
  have hψ : Spec.map ψ = hW.fromSpec ≫ T.hom := Spec.map_preimage _
  let _ : Algebra k A := ψ.hom.toAlgebra
  have het : Algebra.Etale k A := by
    have : Etale (Spec.map ψ) := by rw [hψ]; infer_instance
    exact RingHom.etale_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Etale)).1 this)
  have : Nontrivial A := by
    have hz : z ∈ Set.range hW.fromSpec := by rw [hW.range_fromSpec]; exact hzW
    obtain ⟨y, -⟩ := hz
    exact PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨y⟩
  obtain ⟨I, _, Ai, _, _, e, hAi⟩ := (Algebra.Etale.iff_exists_algEquiv_prod k A).1 het
  have hI : Nonempty I := by
    by_contra hI
    rw [not_nonempty_iff] at hI
    exact not_subsingleton A e.toEquiv.subsingleton
  obtain ⟨i⟩ := hI
  obtain ⟨h₁, h₂⟩ := hAi i
  let j : A →ₐ[k] Ai i := (Pi.evalAlgHom k Ai i).comp e.toAlgHom
  refine ⟨Ai i, inferInstance, inferInstance, h₁, h₂,
    ⟨Over.homMk (Spec.map (CommRingCat.ofHom j.toRingHom) ≫ hW.fromSpec) ?_⟩⟩
  change (Spec.map (CommRingCat.ofHom j.toRingHom) ≫ hW.fromSpec) ≫ T.hom =
    Spec.map (CommRingCat.ofHom (algebraMap k (Ai i)))
  rw [Category.assoc, ← hψ, ← Spec.map_comp]
  congr 1
  ext c
  exact j.commutes c

/-- A `k`-point of an algebraic space over `Spec k` lifts, over a finite Galois extension
`K/k`, to a `K`-point of an affine scheme with an étale map to the space. -/
theorem exists_galois_chart (X : AlgebraicSpace (Spec (CommRingCat.of k)))
    (x : RingPoints k X k) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K), FiniteDimensional k K ∧ IsGalois k K ∧
      ∃ (V : Over (Spec (CommRingCat.of k))) (a : (schemeYoneda _).obj V ⟶ X.presheaf),
        IsAffine V.left ∧ _root_.AlgebraicGeometry.IsSeparated V.hom ∧
        (schemeYoneda _).relativelyRepresentable a ∧ IsEtale a ∧
        ∃ v : specOver k K ⟶ V,
          (schemeYoneda _).map v ≫ a =
            (schemeYoneda _).map (specOverMap (Algebra.ofId k K)) ≫
              (uliftYonedaEquiv.symm x :
                (schemeYoneda (Spec (CommRingCat.of k))).obj (ringTest k k) ⟶ X.presheaf) := by
  obtain ⟨U₀, a₀, ha₀, he₀, hs₀⟩ := X.exists_atlas
  let xh : (schemeYoneda (Spec (CommRingCat.of k))).obj (ringTest k k) ⟶ X.presheaf :=
    uliftYonedaEquiv.symm x
  let P := ha₀.pullback xh
  let p : P ⟶ ringTest k k := ha₀.snd xh
  let q : P ⟶ U₀ := Functor.relativelyRepresentable.fst' ha₀ xh
  have hsq : IsPullback ((schemeYoneda _).map q) ((schemeYoneda _).map p) a₀ xh :=
    Functor.relativelyRepresentable.isPullback' ha₀ xh
  have hpe : Etale p.left := he₀.projection xh _ p hsq
  have hps : Surjective p.left := hs₀.projection xh _ p hsq
  -- `P` is étale over `Spec k` and nonempty
  have : Etale P.hom := by
    rw [← ringTest_self_left p]
    exact hpe
  have : Nonempty P.left := by
    obtain ⟨y⟩ : Nonempty (Spec (CommRingCat.of k)) := inferInstance
    obtain ⟨z, -⟩ := hps.surj y
    exact ⟨z⟩
  obtain ⟨L, _, _, hL, hLs, ⟨w₀⟩⟩ := exists_separable_point P
  obtain ⟨K, _, _, hK, hKg, ⟨ι⟩⟩ := exists_galois_of_separable (k := k) L
  let v₁ : specOver k K ⟶ U₀ := specOverMap ι ≫ w₀ ≫ q
  have hv₁ : (schemeYoneda _).map v₁ ≫ a₀ =
      (schemeYoneda _).map (specOverMap (Algebra.ofId k K)) ≫ xh := by
    have hp : (specOverMap ι ≫ w₀ ≫ p : specOver k K ⟶ ringTest k k) =
        specOverMap (Algebra.ofId k K) := ringTest_self_hom_ext _ _
    simp only [v₁, Functor.map_comp, Category.assoc, hsq.w]
    rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
    exact congrArg (fun t => (schemeYoneda _).map t ≫ xh) ((Category.assoc _ _ _).trans hp)
  -- an affine open of `U₀` through the image of `v₁`
  obtain ⟨y₀⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  obtain ⟨O, hO, hyO, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show v₁.left y₀ ∈ (⊤ : U₀.left.Opens) from trivial)
  have hrange : Set.range v₁.left ⊆ Set.range O.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    rwa [Subsingleton.elim (α := Spec (CommRingCat.of K)) y y₀]
  let V : Over (Spec (CommRingCat.of k)) := Over.mk (O.ι ≫ U₀.hom)
  let ιV : V ⟶ U₀ := Over.homMk O.ι rfl
  have : IsAffine V.left := hO
  let v : specOver k K ⟶ V := Over.homMk (IsOpenImmersion.lift O.ι v₁.left hrange) (by
    change IsOpenImmersion.lift O.ι v₁.left hrange ≫ O.ι ≫ U₀.hom = _
    rw [IsOpenImmersion.lift_fac_assoc]
    exact Over.w v₁)
  have hv : v ≫ ιV = v₁ := Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)
  have hetV : IsEtale ((schemeYoneda _).map ιV ≫ a₀) :=
    IsEtale.comp (isEtale_map ιV (inferInstanceAs (Etale O.ι))) he₀
  refine ⟨K, inferInstance, inferInstance, hK, hKg, V, (schemeYoneda _).map ιV ≫ a₀,
    inferInstance,
    _root_.AlgebraicGeometry.IsSeparated.of_isAffineHom (h := isAffineHom_of_isAffine _),
    hetV.representable, hetV, v, ?_⟩
  rw [← Functor.map_comp_assoc, hv, hv₁]

/-- A `K`-point of an affine scheme over `Spec k`, for a finite Galois extension `K/k`, that
is invariant under `Gal(K/k)` is the base change of a `k`-point. -/
theorem exists_desc_of_galois_invariant {V : Over (Spec (CommRingCat.of k))} [IsAffine V.left]
    {K : Type u} [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : specOver k K ⟶ V) (hw : ∀ σ : K ≃ₐ[k] K, specOverMap σ.toAlgHom ≫ w = w) :
    ∃ u : ringTest k k ⟶ V, specOverMap (Algebra.ofId k K) ≫ u = w := by
  let φ : Γ(V.left, ⊤) ⟶ CommRingCat.of K := Spec.preimage (w.left ≫ V.left.isoSpec.hom)
  have hφ : Spec.map φ = w.left ≫ V.left.isoSpec.hom := Spec.map_preimage _
  have hfix : ∀ (σ : K ≃ₐ[k] K) (a : Γ(V.left, ⊤)), σ (φ a) = φ a := by
    intro σ a
    have h1 : Spec.map (φ ≫ CommRingCat.ofHom σ.toAlgHom.toRingHom) = Spec.map φ := by
      rw [Spec.map_comp, hφ, ← Category.assoc]
      congr 1
      exact congrArg CommaMorphism.left (hw σ)
    exact congrArg (fun g => g.hom a) (Spec.map_injective h1)
  have hmem : ∀ a, φ a ∈ Set.range (algebraMap k K) := fun a =>
    (IsGalois.mem_range_algebraMap_iff_fixed (φ a)).2 fun σ => hfix σ a
  choose c hc using hmem
  have hinj := (algebraMap k K).injective
  let φ' : Γ(V.left, ⊤) →+* k :=
    { toFun := c
      map_one' := hinj (by rw [hc, map_one, map_one])
      map_mul' := fun a b => hinj (by rw [map_mul, hc, hc, hc, map_mul])
      map_zero' := hinj (by rw [hc, map_zero, map_zero])
      map_add' := fun a b => hinj (by rw [map_add, hc, hc, hc, map_add]) }
  have hφ' : CommRingCat.ofHom φ' ≫ CommRingCat.ofHom (algebraMap k K) = φ := by
    ext a
    exact hc a
  -- morphisms out of `Spec k` are detected after the base change to `Spec K`
  have key : ∀ g₁ g₂ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k),
      Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ g₁ =
        Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ g₂ → g₁ = g₂ := by
    intro g₁ g₂ h
    rw [← Spec.map_preimage g₁, ← Spec.map_preimage g₂, ← Spec.map_comp,
      ← Spec.map_comp] at h
    rw [← Spec.map_preimage g₁, ← Spec.map_preimage g₂]
    congr 1
    ext a
    exact hinj (congrArg (fun g => g.hom a) (Spec.map_injective h))
  have hleft : Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫
      (Spec.map (CommRingCat.ofHom φ') ≫ V.left.isoSpec.inv) = w.left := by
    rw [← Category.assoc, ← Spec.map_comp, hφ', hφ, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have h1 : Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫
      ((Spec.map (CommRingCat.ofHom φ') ≫ V.left.isoSpec.inv) ≫ V.hom) =
        Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ 𝟙 _ := by
    rw [Category.comp_id, ← Category.assoc, hleft]
    exact Over.w w
  refine ⟨Over.homMk (Spec.map (CommRingCat.ofHom φ') ≫ V.left.isoSpec.inv)
    ((key _ _ h1).trans ringTest_self_hom.symm), ?_⟩
  exact Over.OverMorphism.ext hleft

/-- For a finite extension `K/k`, the `k`-points of an algebraic space over `Spec k` inject
into its `K`-points: `Spec K → Spec k` is an fppf cover and the space is an fppf sheaf. -/
theorem changeRing_injective (X : AlgebraicSpace (Spec (CommRingCat.of k)))
    (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K] :
    Function.Injective (RingPoints.changeRing (X := X) (Algebra.ofId k K)) := by
  intro x₁ x₂ h
  let π := ringTestMap k (Algebra.ofId k K)
  have : Flat π.left := inferInstanceAs (Flat (specOver k K).hom)
  have : LocallyOfFinitePresentation π.left :=
    inferInstanceAs (LocallyOfFinitePresentation (specOver k K).hom)
  have : Surjective π.left := inferInstanceAs (Surjective (specOver k K).hom)
  have hsh := (isSheaf_iff_isSheaf_of_type _ _).1 X.toSheaf.property _
    (generate_singleton_mem_fppfTopology π)
  apply hsh.isSeparatedFor.ext
  rintro T f ⟨Z, g, _, ⟨⟩, rfl⟩
  exact (X.pullback_comp g π x₁).trans
    ((congrArg (X.pullback g) h).trans (X.pullback_comp g π x₂).symm)

end GaloisChartPoint

end Langlands.AlgebraicGeometry.AlgebraicSpace
