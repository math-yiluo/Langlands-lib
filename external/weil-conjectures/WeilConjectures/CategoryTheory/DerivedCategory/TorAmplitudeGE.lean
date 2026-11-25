/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatDevissage
public import WeilConjectures.CategoryTheory.DerivedCategory.KFlatShortExact

/-!
# Tor amplitude in `[a, ∞)` and bounded below K-flat models

Let `C` be a closed braided monoidal Grothendieck abelian category with functorial flat
resolutions. An object `K` of `D(C)` has *Tor amplitude in `[a, ∞)`*
(`DerivedCategory.torAmplitudeGE`) if `K ⊗ᴸ F[0]` vanishes in degrees `< a` for every object
`F` of `C`. We show that this holds exactly when `K` is represented by a K-flat complex of flat
objects vanishing in degrees `< a` (`DerivedCategory.torAmplitudeGE_iff_exists_kFlat`, Stacks
Tag 0F1M).

The model is the canonical truncation `τ^{≥ a} P` of a K-flat flat resolution `P` of `K`: its
term in degree `a` is the cokernel of `P^{a-1} ⟶ P^a`, which is flat by the Tor criterion
`CategoryTheory.ObjectProperty.flat_opcycles_of_exactAt`, and the kernel of `P ⟶ τ^{≥ a} P` is
a bounded above complex of flat objects, so `τ^{≥ a} P` is K-flat by
`CochainComplex.kFlat_of_shortExact`. The same argument applies after any exact functor
preserving flat objects (`CochainComplex.kFlat_mapHomologicalComplex_obj_truncGE`).
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

universe w v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]

omit [IsGrothendieckAbelian.{v} C] in
/-- If `P` is a complex of flat objects such that `P ⊗ F` is exact in degree `a - 1` for every
object `F`, then the canonical truncation `τ^{≥ a} P` is a complex of flat objects: its term in
degree `a` is the cokernel of `P^{a-1} ⟶ P^a`. -/
lemma flat_truncGE_X (P : CochainComplex C ℤ) (a : ℤ) (hP : ∀ n, ObjectProperty.flat (P.X n))
    (hex : ∀ F : C, (((tensorRight F).mapHomologicalComplex (.up ℤ)).obj P).ExactAt (a - 1))
    (n : ℤ) : ObjectProperty.flat ((P.truncGE a).X n) := by
  obtain hn | rfl | hn := lt_trichotomy n a
  · exact ObjectProperty.flat_of_isZero (CochainComplex.isZero_of_isStrictlyGE _ a n hn)
  · exact ObjectProperty.prop_of_iso _ (P.truncGEXIsoOpcycles n).symm
      (ObjectProperty.flat_opcycles_of_exactAt P n (hP _) (hP _) hex)
  · exact ObjectProperty.prop_of_iso _ (P.truncGEXIso a n hn).symm (hP n)

/-- The short exact sequence `0 ⟶ ker π ⟶ P ⟶ τ^{≥ a} P ⟶ 0`, `π` being the projection to the
canonical truncation. -/
noncomputable abbrev shortComplexTruncGE (P : CochainComplex C ℤ) (a : ℤ) :
    ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (kernel.ι (P.πTruncGE a)) (P.πTruncGE a) (kernel.condition _)

omit [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C] in
lemma shortExact_shortComplexTruncGE (P : CochainComplex C ℤ) (a : ℤ) :
    (P.shortComplexTruncGE a).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _))
    inferInstance inferInstance

variable [Abelian.HasFunctorialFlatResolution C]

/-- Let `G : C ⥤ D` be an exact functor preserving flat objects and `P` a complex of flat objects
such that `G(P)` is K-flat and `P ⊗ F` is exact in degree `a - 1` for every object `F`. Then
`G(τ^{≥ a} P)` is K-flat: it is the quotient of `G(P)` by `G(ker π)`, a bounded above complex of
flat objects, and its terms are flat. -/
lemma kFlat_mapHomologicalComplex_obj_truncGE {D : Type*} [Category.{v} D] [Abelian D]
    [IsGrothendieckAbelian.{v} D] [MonoidalCategory D] [MonoidalPreadditive D]
    [MonoidalClosed D] [BraidedCategory D] [Abelian.HasFunctorialFlatResolution D]
    (G : C ⥤ D) [G.Additive] [G.PreservesFlat] [PreservesFiniteLimits G]
    [PreservesFiniteColimits G]
    (P : CochainComplex C ℤ) (a : ℤ) (hP : ∀ n, ObjectProperty.flat (P.X n))
    (hGP : (HomologicalComplex.quasiIso D (.up ℤ)).kFlat ((G.mapHomologicalComplex _).obj P))
    (hex : ∀ F : C, (((tensorRight F).mapHomologicalComplex (.up ℤ)).obj P).ExactAt (a - 1)) :
    (HomologicalComplex.quasiIso D (.up ℤ)).kFlat
      ((G.mapHomologicalComplex _).obj (P.truncGE a)) := by
  have hS := P.shortExact_shortComplexTruncGE a
  have hT : ((P.shortComplexTruncGE a).map (G.mapHomologicalComplex (.up ℤ))).ShortExact :=
    hS.map_of_exact _
  have hE := P.flat_truncGE_X a hP hex
  -- the kernel of `P ⟶ τ^{≥ a} P` has flat terms and vanishes above `a`
  have hK (n : ℤ) : ObjectProperty.flat ((kernel (P.πTruncGE a)).X n) :=
    ObjectProperty.flat_of_shortExact (hS.map_of_exact (HomologicalComplex.eval _ _ n))
      (hP n) (hE n)
  have : (kernel (P.πTruncGE a)).IsStrictlyLE a := by
    rw [isStrictlyLE_iff]
    intro n hn
    have hSn := hS.map_of_exact (HomologicalComplex.eval _ _ n)
    have := hSn.mono_f
    have : IsIso ((P.πTruncGE a).f n) := P.isIso_πTruncGE_f a n (by lia)
    refine IsZero.of_mono_eq_zero ((kernel.ι (P.πTruncGE a)).f n) ?_
    rw [← cancel_mono ((P.πTruncGE a).f n), zero_comp, ← HomologicalComplex.comp_f,
      kernel.condition, HomologicalComplex.zero_f]
  have : IsStrictlyLE ((G.mapHomologicalComplex _).obj (kernel (P.πTruncGE a))) a :=
    (isStrictlyLE_iff _ a).2 fun i hi ↦ G.map_isZero (isZero_of_isStrictlyLE _ a i hi)
  have h₁ : (HomologicalComplex.quasiIso D (.up ℤ)).kFlat
      ((G.mapHomologicalComplex _).obj (kernel (P.πTruncGE a))) := by
    have (X : D) : PreservesColimitsOfShape ℤ ((curriedTensor D).flip.obj X) :=
      preservesColimitsOfShape_of_natIso (F := tensorLeft X)
        (NatIso.ofComponents (fun Y ↦ β_ X Y) (by intros; simp [curriedTensor]))
    exact kFlat_of_isStrictlyLE_of_flat _ a fun n ↦
      Functor.PreservesFlat.flat_obj (F := G) (hK n)
  exact kFlat_of_shortExact (S := (P.shortComplexTruncGE a).map (G.mapHomologicalComplex (.up ℤ)))
    hT h₁ hGP fun n ↦ Functor.PreservesFlat.flat_obj (F := G) (hE n)

/-- If `P` is a K-flat complex of flat objects such that `P ⊗ F` is exact in degree `a - 1`
for every object `F`, then its canonical truncation `τ^{≥ a} P` is K-flat. -/
lemma kFlat_truncGE (P : CochainComplex C ℤ) (a : ℤ) (hP : ∀ n, ObjectProperty.flat (P.X n))
    (hPk : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P)
    (hex : ∀ F : C, (((tensorRight F).mapHomologicalComplex (.up ℤ)).obj P).ExactAt (a - 1)) :
    (HomologicalComplex.quasiIso C (.up ℤ)).kFlat (P.truncGE a) := by
  have : (𝟭 C).PreservesFlat := ⟨id⟩
  have h := kFlat_mapHomologicalComplex_obj_truncGE (𝟭 C) P a hP
    (ObjectProperty.prop_of_iso _ ((Functor.mapHomologicalComplexIdIso C _).app P).symm hPk) hex
  exact ObjectProperty.prop_of_iso _ ((Functor.mapHomologicalComplexIdIso C _).app _) h

end CochainComplex

namespace DerivedCategory

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasDerivedCategory.{w} C] [Abelian.HasFunctorialFlatResolution C]

/-- An object `M` of `D(C)` has *Tor amplitude in `[a, ∞)`* if for every object `F` of `C` the
derived tensor product `M ⊗ᴸ F[0]` vanishes in degrees `< a` (Stacks, Tag 0651). -/
def torAmplitudeGE (a : ℤ) : ObjectProperty (DerivedCategory C) :=
  fun M ↦ ∀ F : C, (M ⊗ (singleFunctor C 0).obj F).IsGE a

variable {C}

lemma torAmplitudeGE_iff (a : ℤ) (M : DerivedCategory C) :
    torAmplitudeGE C a M ↔ ∀ F : C, (M ⊗ (singleFunctor C 0).obj F).IsGE a :=
  Iff.rfl

/-- Tor amplitude in `[a, ∞)`, in terms of the vanishing of homology objects. -/
lemma torAmplitudeGE_iff_forall_isZero (a : ℤ) (M : DerivedCategory C) :
    torAmplitudeGE C a M ↔ ∀ (F : C) (q : ℤ), q < a →
      IsZero ((homologyFunctor C q).obj (M ⊗ (singleFunctor C 0).obj F)) :=
  forall_congr' fun _ ↦ isGE_iff _ a

/-- Tor amplitude is invariant under isomorphism. -/
instance (a : ℤ) : (torAmplitudeGE C a).IsClosedUnderIsomorphisms where
  of_iso e hM F := by
    have := hM F
    exact TStructure.t.isGE_of_iso (whiskerRightIso e _) a

/-- Shrinking the interval preserves Tor amplitude. -/
lemma torAmplitudeGE.mono {a a' : ℤ} (ha : a' ≤ a) {M : DerivedCategory C}
    (hM : torAmplitudeGE C a M) : torAmplitudeGE C a' M :=
  fun F ↦ by
    have := hM F
    exact TStructure.t.isGE_of_ge _ a' a ha

/-- Tor amplitude in `[a, b]` implies Tor amplitude in `[a, ∞)`. -/
lemma torAmplitudeGE_of_torAmplitudeIn {a b : ℤ} {M : DerivedCategory C}
    (hM : torAmplitudeIn C a b M) : torAmplitudeGE C a M :=
  fun F ↦ (hM F).1

/-- An object of Tor amplitude in `[a, ∞)` vanishes in degrees `< a`: test against the unit. -/
lemma isGE_of_torAmplitudeGE {a : ℤ} {K : DerivedCategory C} (hK : torAmplitudeGE C a K) :
    K.IsGE a :=
  have := hK (𝟙_ C)
  TStructure.t.isGE_of_iso (whiskerLeftIso K (singleFunctorObjUnitIso C) ≪≫ ρ_ K) a

/-- A K-flat complex vanishing in degrees `< a` has Tor amplitude in `[a, ∞)`. -/
lemma torAmplitudeGE_Q_obj_of_kFlat (P : CochainComplex C ℤ) (a : ℤ) [P.IsStrictlyGE a]
    (hP : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P) :
    torAmplitudeGE C a (Q.obj P) := fun F ↦ by
  have := isGE_Q_obj_tensor_of_kFlat P hP a ((singleFunctor C 0).obj F) 0
  rwa [add_zero] at this

/-- For a K-flat complex `P` with `Q(P) ⊗ᴸ F[0]` vanishing in degrees `< a`, the complex
`P ⊗ F` is exact in degree `a - 1`. -/
lemma exactAt_tensorRight_of_torAmplitudeGE (P : CochainComplex C ℤ)
    (hP : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P) {a : ℤ}
    (hK : torAmplitudeGE C a (Q.obj P)) (F : C) :
    (((tensorRight F).mapHomologicalComplex (.up ℤ)).obj P).ExactAt (a - 1) := by
  have := hK F
  have : (Q.obj (((tensorRight F).mapHomologicalComplex (.up ℤ)).obj P)).IsGE a :=
    TStructure.t.isGE_of_iso (QObjTensorSingleFunctorObjIso P hP F) a
  rw [isGE_Q_obj_iff] at this
  exact CochainComplex.exactAt_of_isGE _ a _ (by lia)

/-- **Bounded below K-flat model** (Stacks, Tag 0F1M). An object of Tor amplitude in `[a, ∞)`
is represented by a K-flat complex of flat objects vanishing in degrees `< a`: the canonical
truncation `τ^{≥ a} P` of a K-flat flat resolution `P`. -/
lemma exists_iso_Q_obj_kFlat_of_torAmplitudeGE {a : ℤ} {K : DerivedCategory C}
    (hK : torAmplitudeGE C a K) :
    ∃ (P : CochainComplex C ℤ) (_ : P.IsStrictlyGE a), (∀ n, ObjectProperty.flat (P.X n)) ∧
      (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P ∧ Nonempty (Q.obj P ≅ K) := by
  have := isGE_of_torAmplitudeGE hK
  obtain ⟨P, π, _, hP, hPk⟩ := CochainComplex.exists_quasiIso_flat_kFlat (Q.objPreimage K)
  have : IsIso (Q.map π) := by rwa [isIso_Q_map_iff_quasiIso]
  let e : Q.obj P ≅ K := asIso (Q.map π) ≪≫ Q.objObjPreimageIso K
  have : P.IsGE a := by
    rw [← isGE_Q_obj_iff]
    exact TStructure.t.isGE_of_iso e.symm a
  have hex := exactAt_tensorRight_of_torAmplitudeGE P hPk
    ((torAmplitudeGE C a).prop_of_iso e.symm hK)
  exact ⟨P.truncGE a, inferInstance, P.flat_truncGE_X a hP hex, P.kFlat_truncGE a hP hPk hex,
    ⟨(asIso (Q.map (P.πTruncGE a))).symm ≪≫ e⟩⟩

/-- An object of `D(C)` has Tor amplitude in `[a, ∞)` exactly when it is represented by a K-flat
complex of flat objects vanishing in degrees `< a` (Stacks, Tag 0F1M). -/
lemma torAmplitudeGE_iff_exists_kFlat (a : ℤ) (K : DerivedCategory C) :
    torAmplitudeGE C a K ↔
      ∃ (P : CochainComplex C ℤ) (_ : P.IsStrictlyGE a), (∀ n, ObjectProperty.flat (P.X n)) ∧
        (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P ∧ Nonempty (Q.obj P ≅ K) := by
  refine ⟨exists_iso_Q_obj_kFlat_of_torAmplitudeGE, ?_⟩
  rintro ⟨P, _, -, hPk, ⟨e⟩⟩
  exact (torAmplitudeGE C a).prop_of_iso e (torAmplitudeGE_Q_obj_of_kFlat P a hPk)

/-- If `K` has Tor amplitude in `[a, ∞)` and `N` vanishes below `c`, then `K ⊗ᴸ N` vanishes
below `a + c`. -/
lemma isGE_tensor_of_torAmplitudeGE {a : ℤ} {K : DerivedCategory C}
    (hK : torAmplitudeGE C a K) (N : DerivedCategory C) (c : ℤ) [N.IsGE c] :
    (K ⊗ N).IsGE (a + c) := by
  obtain ⟨P, _, -, hPk, ⟨e⟩⟩ := exists_iso_Q_obj_kFlat_of_torAmplitudeGE hK
  have := isGE_Q_obj_tensor_of_kFlat P hPk a N c
  exact TStructure.t.isGE_of_iso (whiskerRightIso e N) _

/-- If `N` vanishes below `c` and `K` has Tor amplitude in `[a, ∞)`, then `N ⊗ᴸ K` vanishes
below `c + a`. -/
lemma isGE_tensor_of_torAmplitudeGE_right {a : ℤ} {K : DerivedCategory C}
    (hK : torAmplitudeGE C a K) (N : DerivedCategory C) (c : ℤ) [N.IsGE c] :
    (N ⊗ K).IsGE (c + a) := by
  obtain ⟨P, _, -, hPk, ⟨e⟩⟩ := exists_iso_Q_obj_kFlat_of_torAmplitudeGE hK
  obtain ⟨L, _, ⟨e'⟩⟩ := N.exists_iso_Q_obj_of_isGE c
  have := CochainComplex.isStrictlyGE_tensorObj L P c a
  exact TStructure.t.isGE_of_iso
    (tensorIso e' e.symm ≪≫ QObjTensorQObjIsoOfKFlatRight L P hPk).symm _

end DerivedCategory
