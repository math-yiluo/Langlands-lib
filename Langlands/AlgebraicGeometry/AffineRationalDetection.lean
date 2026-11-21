import Langlands.AlgebraicGeometry.ClosedRationalPoints
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Joint injectivity of evaluations after scalar extension -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

noncomputable section

namespace Langlands.AlgebraicGeometry

section Tensor

variable {K R B : Type u} [Field K] [CommRing R] [CommRing B] [Algebra K R] [Algebra K B]

/-- Extension of evaluation `R → K` to `R ⊗[K] B`, with target `B`. -/
def tensorEvaluation (e : R →ₐ[K] K) : R ⊗[K] B →ₐ[K] B :=
  Algebra.TensorProduct.productMap ((Algebra.ofId K B).comp e) (AlgHom.id K B)

/-- A family of jointly injective field evaluations stays jointly injective after
any extension of scalars; the coefficient ring is allowed to be nonreduced. -/
lemma tensorEvaluations_separate {I : Type v} (e : I → R →ₐ[K] K)
    (he : ∀ r, (∀ i, e i r = 0) → r = 0) (t : R ⊗[K] B)
    (ht : ∀ i, tensorEvaluation (B := B) (e i) t = 0) : t = 0 := by
  classical
  let b := Module.Free.chooseBasis K B
  let E := TensorProduct.equivFinsuppOfBasisRight (M := R) b
  suffices hE : E t = 0 by
    exact E.injective (hE.trans E.map_zero.symm)
  ext j
  change E t j = 0
  apply he
  intro i
  have hcoeff (z : R ⊗[K] B) : b.repr (tensorEvaluation (e i) z) j = e i (E z j) := by
    induction z using TensorProduct.inductionOn with
    | tmul r s =>
      rw [tensorEvaluation, Algebra.TensorProduct.productMap_apply_tmul]
      change b.repr (algebraMap K B (e i r) * s) j =
        e i (TensorProduct.equivFinsuppOfBasisRight b (r ⊗ₜ[K] s) j)
      rw [← Algebra.smul_def, map_smul, Finsupp.smul_apply,
        TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, map_smul]
      exact mul_comm _ _
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  have h := hcoeff t
  rw [ht i, map_zero, Finsupp.zero_apply] at h
  exact h.symm

local notation "Specᵣ " R:arg => Spec (CommRingCat.of R)

/-- An affine closed immersion through which all scalar extensions of a jointly
injective family of field evaluations factor is an isomorphism. -/
lemma isIso_of_factors_tensorEvaluations {I : Type v} (e : I → R →ₐ[K] K)
    (he : ∀ r, (∀ i, e i r = 0) → r = 0)
    {Z : Scheme.{u}} (q : Z ⟶ Specᵣ (R ⊗[K] B)) [IsClosedImmersion q]
    (h : ∀ i, ∃ t : Specᵣ B ⟶ Z,
      t ≫ q = Spec.map (CommRingCat.ofHom (tensorEvaluation (e i)).toRingHom)) : IsIso q := by
  apply IsClosedImmersion.isIso_iff_ker_eq_bot.mpr
  apply Scheme.IdealSheafData.ext_of_isAffine
  change q.ker.ideal ⟨⊤, isAffineOpen_top _⟩ = ⊥
  rw [Scheme.Hom.ker_apply, ← le_bot_iff]
  intro s hs
  rw [Ideal.mem_bot]
  let iso := Scheme.ΓSpecIso (CommRingCat.of (R ⊗[K] B))
  apply iso.commRingCatIsoToRingEquiv.injective
  change iso.hom s = iso.hom 0
  rw [map_zero]
  apply tensorEvaluations_separate e he
  intro i
  obtain ⟨t, ht⟩ := h i
  let φ := CommRingCat.ofHom (tensorEvaluation (B := B) (e i)).toRingHom
  change φ (iso.hom s) = 0
  have hs' : q.appTop s = 0 := RingHom.mem_ker.mp hs
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply, ← ht,
    Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hs', map_zero, map_zero]

end Tensor

open MonoidalCategory CartesianMonoidalCategory

section Slices

local notation "Specᵣ " R:arg => Spec (CommRingCat.of R)

variable {K : Type u} [Field K]

/-- The slice of `X ×[K] T` at a rational point of `X`, with parameter scheme `T`. -/
def rationalSlice {X : Over (Specᵣ K)} (x : 𝟙_ (Over (Specᵣ K)) ⟶ X)
    (T : Over (Specᵣ K)) : T ⟶ X ⊗ T :=
  lift (toUnit T ≫ x) (𝟙 T)

@[reassoc (attr := simp)]
lemma rationalSlice_fst {X : Over (Specᵣ K)} (x : 𝟙_ (Over (Specᵣ K)) ⟶ X)
    (T : Over (Specᵣ K)) : rationalSlice x T ≫ fst _ _ = toUnit T ≫ x := by
  simp [rationalSlice]

@[reassoc (attr := simp)]
lemma rationalSlice_snd {X : Over (Specᵣ K)} (x : 𝟙_ (Over (Specᵣ K)) ⟶ X)
    (T : Over (Specᵣ K)) : rationalSlice x T ≫ snd _ _ = 𝟙 T := by
  simp [rationalSlice]

@[reassoc]
lemma rationalSlice_tensorHom {X X' T T' : Over (Specᵣ K)}
    (x : 𝟙_ (Over (Specᵣ K)) ⟶ X) (a : X ⟶ X') (b : T ⟶ T') :
    rationalSlice x T ≫ (a ⊗ₘ b) = b ≫ rationalSlice (x ≫ a) T' := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [Category.assoc]

private def pointAlgHom {R : Type u} [CommRing R] [Algebra K R]
    (x : 𝟙_ (Over (Specᵣ K)) ⟶ Over.mk (Spec.algebraMap K R)) : R →ₐ[K] K where
  __ := (Spec.preimage x.left).hom
  commutes' a := by
    have h := congrArg Spec.preimage (Over.w x)
    change Spec.preimage (x.left ≫ Spec.algebraMap K R) = Spec.preimage (𝟙 (Specᵣ K)) at h
    simp only [Spec.algebraMap, Spec.preimage_comp, Spec.preimage_map, Spec.preimage_id] at h
    exact congrArg (fun q : CommRingCat.of K ⟶ CommRingCat.of K ↦ q a) h

private lemma pointAlgHom_specMap {R : Type u} [CommRing R] [Algebra K R]
    (x : 𝟙_ (Over (Specᵣ K)) ⟶ Over.mk (Spec.algebraMap K R)) :
    Spec.map (CommRingCat.ofHom (pointAlgHom x).toRingHom) = x.left :=
  Spec.map_preimage _

private lemma rationalEval_separate [IsAlgClosed K]
    {X : Over (Specᵣ K)} [IsReduced X.left] [LocallyOfFiniteType X.hom]
    {R : Type u} [CommRing R] [Algebra K R]
    (j : Over.mk (Spec.algebraMap K R) ⟶ X) [IsOpenImmersion j.left]
    (U : X.left.Opens) (hU : Dense (U : Set X.left)) (r : R)
    (hr : ∀ x : 𝟙_ (Over (Specᵣ K)) ⟶ Over.mk (Spec.algebraMap K R),
      (x ≫ j).left (IsLocalRing.closedPoint K) ∈ U → pointAlgHom x r = 0) : r = 0 := by
  let V : (Specᵣ R).Opens := PrimeSpectrum.basicOpen r
  by_contra hn
  have : _root_.IsReduced R := (affine_isReduced_iff (CommRingCat.of R)).mp
    (isReduced_of_isOpenImmersion j.left)
  have hV : (V : Set (Specᵣ R)).Nonempty := by
    by_contra hz
    have hz' := (TopologicalSpace.Opens.not_nonempty_iff_eq_bot V).mp hz
    exact hn ((PrimeSpectrum.basicOpen_eq_bot_iff r).mp hz').eq_zero
  have hVU : ((V ⊓ j.left ⁻¹ᵁ U : (Specᵣ R).Opens) : Set (Specᵣ R)).Nonempty := by
    obtain ⟨_, ⟨a, ha, rfl⟩, hb⟩ :=
      hU.inter_open_nonempty (j.left '' (V : Set (Specᵣ R)))
        (j.left.isOpenEmbedding.isOpenMap _ V.isOpen) (hV.image j.left)
    exact ⟨a, ha, hb⟩
  have : LocallyOfFiniteType (Over.mk (Spec.algebraMap K R)).hom := by
    rw [← Over.w j]
    infer_instance
  obtain ⟨x, hx⟩ := ClosedRationalPoints.exists_rationalPoint_mem
    (X := Over.mk (Spec.algebraMap K R)) _ hVU
  have hxv : x.left (IsLocalRing.closedPoint K) ∈ V := hx.1
  have hxU : (x ≫ j).left (IsLocalRing.closedPoint K) ∈ U := hx.2
  apply (PrimeSpectrum.mem_basicOpen _ _).mp hxv
  rw [← pointAlgHom_specMap x]
  change pointAlgHom x r ∈ (IsLocalRing.closedPoint K).asIdeal
  rw [hr x hxU]
  exact Ideal.zero_mem _

private lemma tensorEvaluation_specMap_inv_fst {R B : Type u} [CommRing R] [CommRing B]
    [Algebra K R] [Algebra K B] (e : R →ₐ[K] K) :
    Spec.map (CommRingCat.ofHom (tensorEvaluation (B := B) e).toRingHom) ≫
      (pullbackSpecIso K R B).inv ≫ pullback.fst _ _ =
      Spec.algebraMap K B ≫ Spec.map (CommRingCat.ofHom e.toRingHom) := by
  rw [pullbackSpecIso_inv_fst, ← Spec.map_comp, Spec.algebraMap, ← Spec.map_comp]
  congr 1
  ext r
  change tensorEvaluation (B := B) e (r ⊗ₜ[K] 1) = algebraMap K B (e r)
  simp [tensorEvaluation]

private lemma tensorEvaluation_specMap_inv_snd {R B : Type u} [CommRing R] [CommRing B]
    [Algebra K R] [Algebra K B] (e : R →ₐ[K] K) :
    Spec.map (CommRingCat.ofHom (tensorEvaluation (B := B) e).toRingHom) ≫
      (pullbackSpecIso K R B).inv ≫ pullback.snd _ _ = 𝟙 _ := by
  rw [pullbackSpecIso_inv_snd, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext b
  change tensorEvaluation (B := B) e (1 ⊗ₜ[K] b) = b
  simp [tensorEvaluation]

private lemma hom_ext_of_rational_slices_affine [IsAlgClosed K]
    {X T Y : Over (Specᵣ K)} [IsReduced X.left] [LocallyOfFiniteType X.hom] [IsSeparated Y.hom]
    (U : X.left.Opens) (hU : Dense (U : Set X.left)) {f g : X ⊗ T ⟶ Y}
    (h : ∀ x : 𝟙_ (Over (Specᵣ K)) ⟶ X,
      x.left (IsLocalRing.closedPoint K) ∈ U → rationalSlice x T ≫ f = rationalSlice x T ≫ g)
    {R B : Type u} [CommRing R] [CommRing B] [Algebra K R] [Algebra K B]
    (j : Over.mk (Spec.algebraMap K R) ⟶ X) [IsOpenImmersion j.left]
    (k : Over.mk (Spec.algebraMap K B) ⟶ T) : (j ⊗ₘ k) ≫ f = (j ⊗ₘ k) ≫ g := by
  let Xr := Over.mk (Spec.algebraMap K R)
  let Tb := Over.mk (Spec.algebraMap K B)
  let a : Xr ⊗ Tb ⟶ Y := (j ⊗ₘ k) ≫ f
  let b : Xr ⊗ Tb ⟶ Y := (j ⊗ₘ k) ≫ g
  let P := {x : 𝟙_ (Over (Specᵣ K)) ⟶ Xr // (x ≫ j).left (IsLocalRing.closedPoint K) ∈ U}
  let e : P → R →ₐ[K] K := fun x ↦ pointAlgHom x.1
  let d : (Xr ⊗ Tb).left ≅ Specᵣ (R ⊗[K] B) := pullbackSpecIso K R B
  let i := equalizer.ι a b
  have hi : IsIso (i.left ≫ d.hom) := by
    refine isIso_of_factors_tensorEvaluations e (fun r hr ↦ ?_) _ (fun x ↦ ?_)
    · exact rationalEval_separate j U hU r fun x hx ↦ hr ⟨x, hx⟩
    · have hx : rationalSlice x.1 Tb ≫ a = rationalSlice x.1 Tb ≫ b := by
        simpa only [a, b, rationalSlice_tensorHom_assoc] using
          congrArg (k ≫ ·) (h (x.1 ≫ j) x.2)
      refine ⟨(equalizer.lift (rationalSlice x.1 Tb) hx).left, ?_⟩
      rw [← Over.comp_left_assoc, equalizer.lift_ι, ← Iso.eq_comp_inv]
      change (rationalSlice x.1 Tb).left =
        Spec.map (CommRingCat.ofHom (tensorEvaluation (e x)).toRingHom) ≫ d.inv
      apply pullback.hom_ext
      · dsimp only [Xr, Tb, Over.mk_hom]
        simp only [rationalSlice, Over.lift_left, pullback.lift_fst, Over.comp_left,
          Over.toUnit_left, Category.assoc, d, e, tensorEvaluation_specMap_inv_fst,
          pointAlgHom_specMap, Over.mk_hom]
      · dsimp only [Xr, Tb, Over.mk_hom]
        simp only [rationalSlice, Over.lift_left, Over.id_left,
          Category.assoc, d, tensorEvaluation_specMap_inv_snd]
        exact pullback.lift_snd _ _ _
  have : IsIso i.left := IsIso.of_isIso_comp_right i.left d.hom
  apply Over.OverMorphism.ext
  change a.left = b.left
  rw [← cancel_epi i.left, ← Over.comp_left, ← Over.comp_left]
  exact congrArg (fun z : equalizer a b ⟶ Y ↦ z.left) (equalizer.condition a b)

/-- Maps from `X ×[K] T` to a separated `K`-scheme are determined by their restrictions to
rational slices through any dense open of a reduced locally finite type `X` over algebraically
closed `K`. No reducedness or finite-type hypothesis is imposed on `T`. -/
lemma hom_ext_of_rational_slices [IsAlgClosed K]
    {X T Y : Over (Specᵣ K)} [IsReduced X.left] [LocallyOfFiniteType X.hom] [IsSeparated Y.hom]
    (U : X.left.Opens) (hU : Dense (U : Set X.left)) {f g : X ⊗ T ⟶ Y}
    (h : ∀ x : 𝟙_ (Over (Specᵣ K)) ⟶ X,
      x.left (IsLocalRing.closedPoint K) ∈ U → rationalSlice x T ≫ f = rationalSlice x T ≫ g) :
    f = g := by
  apply Over.OverMorphism.ext
  let 𝒰 := Scheme.Pullback.openCoverOfLeftRight X.left.affineCover T.left.affineCover X.hom T.hom
  apply 𝒰.hom_ext
  rintro ⟨i, l⟩
  let R : CommRingCat.{u} := (X.left.local_affine i).choose_spec.choose
  let B : CommRingCat.{u} := (T.left.local_affine l).choose_spec.choose
  let j : Spec R ⟶ X.left := X.left.affineCover.f i
  let k : Spec B ⟶ T.left := T.left.affineCover.f l
  let : Algebra K R := (Spec.preimage (j ≫ X.hom)).hom.toAlgebra
  let : Algebra K B := (Spec.preimage (k ≫ T.hom)).hom.toAlgebra
  have hj : Spec.algebraMap K R = j ≫ X.hom := Spec.map_preimage _
  have hk : Spec.algebraMap K B = k ≫ T.hom := Spec.map_preimage _
  let jo : Over.mk (Spec.algebraMap K R) ⟶ X := Over.homMk j hj.symm
  let ko : Over.mk (Spec.algebraMap K B) ⟶ T := Over.homMk k hk.symm
  have : IsOpenImmersion jo.left := inferInstanceAs (IsOpenImmersion (X.left.affineCover.f i))
  have he := congrArg (fun a : _ ⟶ Y ↦ a.left) (hom_ext_of_rational_slices_affine U hU h jo ko)
  let d := pullback.congrHom hj.symm hk.symm
  have hd : d.hom ≫ (jo ⊗ₘ ko).left = 𝒰.f ⟨i, l⟩ := by
    simp [d, 𝒰, Over.tensorHom_left, pullback.map_comp, jo, ko, j, k]
    rfl
  simpa only [Over.comp_left, ← Category.assoc, hd] using! congrArg (d.hom ≫ ·) he

end Slices

end Langlands.AlgebraicGeometry
