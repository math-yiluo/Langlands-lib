import Langlands.AlgebraicGeometry.AlgebraicSpace.FieldPointEtaleLift
import Langlands.AlgebraicGeometry.PointTopology.EtaleAlgHomCount

/-!
# Fibres of an étale chart of a quasi-separated space are uniformly bounded

Let `X` be a quasi-separated algebraic space over `Spec C` and `a : h_V → X` an étale chart
from an affine scheme `V`. There is a bound `D` such that, for every field `L` with a
`C`-algebra structure and every `L`-point `s` of `V`, at most `D` distinct `L`-points of `V`
have the same image in `X` as `s`.

Such points are the `L`-points of `V ×_X V` over `s` along the second projection. The overlap
`V ×_X V` is quasi-compact because `X` is quasi-separated: its comparison map to `V ×_C V` is
the base change of the diagonal of `X`. It is covered by finitely many affine opens, each
étale over `V`, and `EtaleAlgHomCount.exists_card_algHom_le` bounds the points in each.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite CartesianMonoidalCategory MonoidalCategory
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology (ringTest RingPoint)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace EtaleChartFibreCount

open FieldPointEtaleLift

section Overlap

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {V : Over S}
variable (a : (schemeYoneda S).obj V ⟶ X.presheaf)

/-- If the diagonal of `X` has represented projections in `P`, then so does the comparison
map `V ×_X V → V ×_S V` of a chart. It is a base change of the diagonal. -/
theorem selfPullbackLift_mem_of_relative_diag (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (hX : (MorphismProperty.inverseImage P (Over.forget S)).relative (schemeYoneda S)
      (diag X.presheaf)) :
    P (lift (selfFst a) (selfSnd a)).left := by
  let g : (schemeYoneda S).obj (V ⊗ V) ⟶ X.presheaf ⨯ X.presheaf :=
    prod.lift ((schemeYoneda S).map (fst V V) ≫ a) ((schemeYoneda S).map (snd V V) ≫ a)
  have hsq := hX.rep.isPullback g
  let ι : hX.rep.pullback g ⟶ V ⊗ V := hX.rep.snd g
  have hP : P ι.left := hX.property_snd g
  have e₁ := congr($(hsq.w) ≫ prod.fst)
  have e₂ := congr($(hsq.w) ≫ prod.snd)
  simp only [Category.assoc, diag, prod.lift_fst, prod.lift_snd, Category.comp_id, g] at e₁ e₂
  have hfst : hX.rep.fst g = (schemeYoneda S).map (ι ≫ fst V V) ≫ a := by
    rw [e₁, Functor.map_comp_assoc]
  have hsnd : hX.rep.fst g = (schemeYoneda S).map (ι ≫ snd V V) ≫ a := by
    rw [e₂, Functor.map_comp_assoc]
  let c : selfPullback a ⟶ V ⊗ V := lift (selfFst a) (selfSnd a)
  let ψ : hX.rep.pullback g ⟶ selfPullback a :=
    selfLift a (ι ≫ fst V V) (ι ≫ snd V V) (hfst.symm.trans hsnd)
  have hψ₁ : ψ ≫ selfFst a = ι ≫ fst V V := Functor.relativelyRepresentable.lift'_fst _ _ _ _
  have hψ₂ : ψ ≫ selfSnd a = ι ≫ snd V V := Functor.relativelyRepresentable.lift'_snd _ _ _ _
  have hw : ((schemeYoneda S).map (selfFst a) ≫ a) ≫ diag X.presheaf =
      (schemeYoneda S).map c ≫ g := by
    apply prod.hom_ext
    · simp only [Category.assoc, diag, prod.lift_fst, Category.comp_id, g, ← Functor.map_comp_assoc,
        c, lift_fst]
    · simp only [Category.assoc, diag, prod.lift_snd, Category.comp_id, g, ← Functor.map_comp_assoc,
        c, lift_snd]
      exact (selfPullback_isPullback a).w
  let φ : selfPullback a ⟶ hX.rep.pullback g := hX.rep.lift _ c hw
  have hφι : φ ≫ ι = c := Functor.relativelyRepresentable.lift_snd _ _ _ _
  have hφψ : φ ≫ ψ = 𝟙 _ := by
    apply Functor.relativelyRepresentable.hom_ext' (X.representable_from_scheme a)
    · change (φ ≫ ψ) ≫ selfFst a = 𝟙 _ ≫ selfFst a
      rw [Category.assoc, hψ₁, ← Category.assoc, hφι, Category.id_comp, lift_fst]
    · change (φ ≫ ψ) ≫ selfSnd a = 𝟙 _ ≫ selfSnd a
      rw [Category.assoc, hψ₂, ← Category.assoc, hφι, Category.id_comp, lift_snd]
  have hψc : ψ ≫ c = ι := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, hψ₁]
    · rw [Category.assoc, lift_snd, hψ₂]
  have hψφ : ψ ≫ φ = 𝟙 _ := by
    apply (schemeYoneda S).map_injective
    apply hsq.hom_ext
    · rw [CategoryTheory.Functor.map_id, Category.id_comp, hfst, ← Functor.map_comp_assoc,
        ← Category.assoc, Category.assoc ψ, hφι, hψc]
    · rw [CategoryTheory.Functor.map_id, Category.id_comp, ← Functor.map_comp, Category.assoc, hφι, hψc]
  have : IsIso φ := ⟨ψ, hφψ, hψφ⟩
  have : IsIso φ.left := (Over.forget S).map_isIso φ
  change P c.left
  rw [← hφι, Over.comp_left]
  exact (MorphismProperty.cancel_left_of_respectsIso P φ.left ι.left).mpr hP

/-- The overlap `V ×_X V` of a chart with quasi-compact `V ×_S V` is quasi-compact when `X`
is quasi-separated. -/
theorem compactSpace_selfPullback (hX : IsQuasiSeparated X) [CompactSpace (V ⊗ V).left] :
    CompactSpace (selfPullback a).left := by
  have : MorphismProperty.RespectsIso (@QuasiCompact.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : QuasiCompact (lift (selfFst a) (selfSnd a)).left :=
    selfPullbackLift_mem_of_relative_diag a (@QuasiCompact.{u}) hX
  exact QuasiCompact.compactSpace_of_compactSpace (lift (selfFst a) (selfSnd a)).left

end Overlap

section Count

/-- **Points of an affine piece of an étale scheme over an affine scheme.** For an étale
morphism `g : Y ⟶ Z` with `Z` affine and an affine open `W` of `Y`, there is a bound on the
number of field-valued points of `W` over a fixed field-valued point of `Z`. -/
theorem exists_card_le_of_etale_affine {Y Z : Scheme.{u}} [IsAffine Z] (g : Y ⟶ Z) [Etale g]
    (W : Y.affineOpens) :
    ∃ D : ℕ, ∀ (L : Type u) [Field L] (z : Spec (CommRingCat.of L) ⟶ Z) (ι : Type u)
      [Fintype ι] (y : ι → (Spec (CommRingCat.of L) ⟶ Y)), Function.Injective y →
      (∀ i, y i ≫ g = z) → (∀ i, Set.range (y i) ⊆ (W : Y.Opens)) → Fintype.card ι ≤ D := by
  have hW : IsAffineOpen (W : Y.Opens) := W.2
  let θ : Γ(Z, ⊤) ⟶ Γ(Y, W) := Spec.preimage (hW.fromSpec ≫ g ≫ Z.isoSpec.hom)
  have hθ : Spec.map θ = hW.fromSpec ≫ g ≫ Z.isoSpec.hom := Spec.map_preimage _
  let _ : Algebra Γ(Z, ⊤) Γ(Y, W) := θ.hom.toAlgebra
  have : Algebra.Etale Γ(Z, ⊤) Γ(Y, W) := by
    have : Etale hW.fromSpec := inferInstance
    have : Etale Z.isoSpec.hom := inferInstance
    have : Etale (Spec.map θ) := by rw [hθ]; infer_instance
    exact RingHom.etale_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Etale)).1 this)
  obtain ⟨D, hD⟩ := PointTopology.EtaleAlgHomCount.exists_card_algHom_le (R := Γ(Z, ⊤)) Γ(Y, W)
  refine ⟨D, fun L _ z ι _ y hy hyz hyW => ?_⟩
  let σ : Γ(Z, ⊤) ⟶ CommRingCat.of L := Spec.preimage (z ≫ Z.isoSpec.hom)
  have hσ : Spec.map σ = z ≫ Z.isoSpec.hom := Spec.map_preimage _
  let _ : Algebra Γ(Z, ⊤) L := σ.hom.toAlgebra
  have hr : ∀ i, Set.range (y i) ⊆ Set.range hW.fromSpec := fun i => by
    rw [hW.range_fromSpec]
    exact hyW i
  let y' : ι → (Spec (CommRingCat.of L) ⟶ Spec Γ(Y, W)) := fun i =>
    IsOpenImmersion.lift hW.fromSpec (y i) (hr i)
  have hy' : ∀ i, y' i ≫ hW.fromSpec = y i := fun i => IsOpenImmersion.lift_fac _ _ _
  let ψ : ι → (Γ(Y, W) ⟶ CommRingCat.of L) := fun i => Spec.preimage (y' i)
  have hψ : ∀ i, Spec.map (ψ i) = y' i := fun i => Spec.map_preimage _
  have hθψ : ∀ i, θ ≫ ψ i = σ := fun i => by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ, hθ, hσ, ← hyz i, ← reassoc_of% (hy' i)]
    simp only [Category.assoc]
  let F : ι → (Γ(Y, W) →ₐ[Γ(Z, ⊤)] L) := fun i =>
    { toRingHom := (ψ i).hom
      commutes' := fun r => congrArg (fun h : Γ(Z, ⊤) ⟶ CommRingCat.of L => h.hom r) (hθψ i) }
  have hF : Function.Injective F := by
    intro i j hij
    apply hy
    have h1 : ψ i = ψ j := by
      ext r
      exact congrArg (fun φ : Γ(Y, W) →ₐ[Γ(Z, ⊤)] L => φ r) hij
    rw [← hy' i, ← hy' j, ← hψ, ← hψ, h1]
  have := (hD L).1
  calc Fintype.card ι = Nat.card ι := (Nat.card_eq_fintype_card).symm
    _ ≤ Nat.card (Γ(Y, W) →ₐ[Γ(Z, ⊤)] L) := Nat.card_le_card_of_injective F hF
    _ ≤ D := (hD L).2

variable {C : Type u} [CommRing C] {X : AlgebraicSpace (Spec (CommRingCat.of C))}
variable {V : Over (Spec (CommRingCat.of C))} (a : (schemeYoneda _).obj V ⟶ X.presheaf)

/-- **Fibres of an étale affine chart are uniformly bounded.** If `X` is quasi-separated and
`a : h_V → X` is étale with `V` affine, there is a bound `D` such that for every field `L`
over `C` and every `L`-point `s` of `V`, any family of pairwise distinct `L`-points of `V`
with the same image in `X` as `s` has at most `D` members. -/
theorem exists_fibre_card_le (hX : IsQuasiSeparated X) (ha : IsEtale a) [IsAffine V.left] :
    ∃ D : ℕ, ∀ (L : Type u) [Field L] [Algebra C L] (s : ringTest C L ⟶ V)
      (ι : Type u) [Fintype ι] (v : ι → (ringTest C L ⟶ V)), Function.Injective v →
      (∀ i, (schemeYoneda _).map (v i) ≫ a = (schemeYoneda _).map s ≫ a) →
        Fintype.card ι ≤ D := by
  classical
  have : IsAffine (V ⊗ V).left := by
    change IsAffine (Limits.pullback V.hom V.hom)
    infer_instance
  have := compactSpace_selfPullback a hX
  have : Etale (selfSnd a).left := ha.projection a _ (selfSnd a) (selfPullback_isPullback a)
  obtain ⟨t, ht⟩ : ∃ t : Finset (selfPullback a).left.affineOpens,
      ∀ x : (selfPullback a).left, ∃ W ∈ t, x ∈ (W : (selfPullback a).left.Opens) := by
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
      (fun W : (selfPullback a).left.affineOpens =>
        ((W : (selfPullback a).left.Opens) : Set (selfPullback a).left))
      (fun W => W.1.isOpen) (fun x _ => by
        obtain ⟨W, hW, hx, -⟩ := exists_isAffineOpen_mem_and_subset
          (show x ∈ (⊤ : (selfPullback a).left.Opens) from trivial)
        exact Set.mem_iUnion.2 ⟨⟨W, hW⟩, hx⟩)
    refine ⟨t, fun x => ?_⟩
    have hx := ht (Set.mem_univ x)
    simp only [Set.mem_iUnion] at hx
    obtain ⟨W, hW, hx⟩ := hx
    exact ⟨W, hW, hx⟩
  choose D hD using fun W : (selfPullback a).left.affineOpens =>
    exists_card_le_of_etale_affine (selfSnd a).left W
  refine ⟨∑ W ∈ t, D W, fun L _ _ s ι _ v hv hva => ?_⟩
  let r : ι → (ringTest C L ⟶ selfPullback a) := fun i => selfLift a (v i) s (hva i)
  have hr₁ : ∀ i, r i ≫ selfFst a = v i := fun i =>
    Functor.relativelyRepresentable.lift'_fst _ _ _ _
  have hr₂ : ∀ i, r i ≫ selfSnd a = s := fun i =>
    Functor.relativelyRepresentable.lift'_snd _ _ _ _
  have hrinj : Function.Injective fun i => (r i).left := by
    intro i j hij
    apply hv
    rw [← hr₁ i, ← hr₁ j, Over.OverMorphism.ext hij]
  obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of L)) := inferInstance
  choose w hwt hw using fun i => ht ((r i).left pt)
  have hrange : ∀ i, Set.range (r i).left ⊆ (w i : (selfPullback a).left.Opens) := by
    rintro i _ ⟨p, rfl⟩
    rw [Subsingleton.elim p pt]
    exact hw i
  have hfib : ∀ W ∈ t, (Finset.univ.filter fun i => w i = W).card ≤ D W := by
    intro W _
    rw [← Fintype.card_subtype]
    refine hD W L s.left {i // w i = W} (fun i => (r i.1).left) ?_ ?_ ?_
    · intro i j hij
      exact Subtype.ext (hrinj hij)
    · intro i
      exact congrArg CommaMorphism.left (hr₂ i.1)
    · intro i
      have h := hrange i.1
      rw [i.2] at h
      exact h
  calc Fintype.card ι = (Finset.univ : Finset ι).card := Finset.card_univ.symm
    _ = ∑ W ∈ t, (Finset.univ.filter fun i => w i = W).card :=
        Finset.card_eq_sum_card_fiberwise fun i _ => hwt i
    _ ≤ ∑ W ∈ t, D W := Finset.sum_le_sum hfib

end Count

end EtaleChartFibreCount

end Langlands.AlgebraicGeometry.AlgebraicSpace
