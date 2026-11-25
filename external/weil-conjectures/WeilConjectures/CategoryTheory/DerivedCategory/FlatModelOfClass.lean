/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.ResolutionByClass
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-!
# Bounded flat models with terms in a class

Let `C` be a closed braided monoidal Grothendieck abelian category with functorial flat
resolutions. `DerivedCategory.exists_iso_Q_obj_flat_of_torAmplitudeIn` represents an object `K`
of Tor amplitude in `[a, b]` by a complex of flat objects concentrated in degrees `[a, b]`.

Here the terms are moreover required to lie in a class `T` of objects closed under kernels and
cokernels, for instance the constructible sheaves on a Noetherian scheme. This is possible when
the cohomology objects of `K` lie in `T` and the flat objects of `T` contain a class `S`,
closed under binary biproducts, which lifts along epimorphisms onto `T`
(`ChainComplex.LiftsAlongEpi`): the flat resolution is then replaced by a resolution by objects
of `S` (`CochainComplex.exists_quasiIso_of_liftsAlongEpi`), and the cokernel `P^a / d(P^{a-1})`
which appears in degree `a` after truncation lies in `T` as a cokernel of a map of objects of
`T`.

## Main results

- `CategoryTheory.ObjectProperty.flat_biprod`: a binary biproduct of flat objects is flat.
- `DerivedCategory.exists_iso_Q_obj_flat_of_torAmplitudeIn_of_liftsAlongEpi`
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

universe w v u

namespace CategoryTheory.ObjectProperty

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [MonoidalCategory A] [BraidedCategory A] [MonoidalClosed A]

/-- A binary biproduct of flat objects is flat. -/
lemma flat_biprod {X Y : A} (hX : flat X) (hY : flat Y) : flat (X ⊞ Y) := by
  let f : ULift.{v} WalkingPair → A := fun j ↦ (Limits.pair X Y).obj ⟨j.down⟩
  refine prop_of_iso _ ?_ (flat_coproduct f (fun ⟨j⟩ ↦ by cases j <;> assumption))
  let g : WalkingPair → A := fun j ↦ (Limits.pair X Y).obj ⟨j⟩
  exact (Sigma.whiskerEquiv (f := f) (g := g) Equiv.ulift (fun _ ↦ Iso.refl _)) ≪≫
    (HasColimit.isoOfNatIso (Discrete.natIso fun _ ↦ Iso.refl _) : ∐ g ≅ X ⨿ Y) ≪≫
    (biprod.isoCoprod X Y).symm

end CategoryTheory.ObjectProperty

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasDerivedCategory.{w} C] [Abelian.HasFunctorialFlatResolution C]

open ZeroObject in
/-- **Bounded flat model with terms in a class.** Let `T` be a property of objects closed under
kernels, cokernels and isomorphisms and containing the zero objects, and let `S` be a property
of flat objects of `T`, closed under binary biproducts and isomorphisms, containing the zero
objects and lifting along epimorphisms onto `T`. Then an object `K` of Tor amplitude in `[a, b]`
whose cohomology objects lie in `T` is represented by a complex of flat objects of `T`
concentrated in degrees `[a, b]`.

The proof is that of `DerivedCategory.exists_iso_Q_obj_flat_of_torAmplitudeIn`, with the flat
resolution replaced by a resolution by objects of `S`
(`CochainComplex.exists_quasiIso_of_liftsAlongEpi`). -/
lemma exists_iso_Q_obj_flat_of_torAmplitudeIn_of_liftsAlongEpi {S T : ObjectProperty C}
    [T.IsClosedUnderKernels] [T.IsClosedUnderCokernels] [T.ContainsZero]
    [T.IsClosedUnderIsomorphisms] [S.ContainsZero] [S.IsClosedUnderIsomorphisms]
    (hST : S ≤ T) (hSf : S ≤ ObjectProperty.flat) (hS : ∀ X Y, S X → S Y → S (X ⊞ Y))
    (hlift : ChainComplex.LiftsAlongEpi S T) {a b : ℤ} {K : DerivedCategory C}
    (hK : torAmplitudeIn C a b K) (hKT : ∀ n, T ((homologyFunctor C n).obj K)) :
    ∃ (P : CochainComplex C ℤ) (_ : P.IsStrictlyGE a) (_ : P.IsStrictlyLE b),
      (∀ n, ObjectProperty.flat (P.X n) ∧ T (P.X n)) ∧ Nonempty (Q.obj P ≅ K) := by
  obtain ⟨hGE, hLE⟩ := homologyConcentratedIn_of_torAmplitudeIn hK
  have : K.IsLE b := hLE
  have : K.IsGE a := hGE
  obtain ⟨L, _, ⟨e⟩⟩ := K.exists_iso_Q_obj_of_isLE b
  have hL (n : ℤ) : T (L.homology n) :=
    T.prop_of_iso ((homologyFunctor C n).mapIso e ≪≫ (homologyFunctorFactors C n).app L) (hKT n)
  obtain ⟨P, _, π, _, hP⟩ := CochainComplex.exists_quasiIso_of_liftsAlongEpi hST hS hlift L b hL
  have : IsIso (Q.map π) := by rwa [isIso_Q_map_iff_quasiIso]
  let e' : Q.obj P ≅ K := asIso (Q.map π) ≪≫ e.symm
  have hPk : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P :=
    CochainComplex.kFlat_of_isStrictlyLE_of_flat P b (fun n ↦ hSf _ (hP n))
  have : P.IsGE a := by
    rw [← isGE_Q_obj_iff]
    exact TStructure.t.isGE_of_iso e'.symm a
  -- `H^{a-1}(P ⊗ F) = H^{a-1}(K ⊗ᴸ F[0]) = 0`
  have hex (F : C) :
      (((tensorRight F).mapHomologicalComplex (.up ℤ)).obj P).ExactAt (a - 1) := by
    have := (hK F).1
    have : (Q.obj (((tensorRight F).mapHomologicalComplex (.up ℤ)).obj P)).IsGE a :=
      TStructure.t.isGE_of_iso
        ((whiskerRightIso e' _).symm ≪≫ QObjTensorSingleFunctorObjIso P hPk F) a
    rw [isGE_Q_obj_iff] at this
    exact CochainComplex.exactAt_of_isGE _ a _
  have hop := ObjectProperty.flat_opcycles_of_exactAt P a (hSf _ (hP _)) (hSf _ (hP _)) hex
  have hopT : T (P.opcycles a) := T.prop_of_isColimit_cokernelCofork
    (P.opcyclesIsCokernel (a - 1) a (by simp)) (hST _ (hP _)) (hST _ (hP _))
  refine ⟨P.truncGE a, inferInstance, ?_, fun n ↦ ?_,
    ⟨(asIso (Q.map (P.πTruncGE a))).symm ≪≫ e'⟩⟩
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    obtain hi' | rfl | hi' := lt_trichotomy i a
    · exact CochainComplex.isZero_of_isStrictlyGE _ a i hi'
    · exact (P.truncGEXIsoOpcycles i).isZero_iff.2
        (IsZero.of_epi (P.pOpcycles i) (P.isZero_of_isStrictlyLE b i hi))
    · exact (P.truncGEXIso a i hi').isZero_iff.2 (P.isZero_of_isStrictlyLE b i hi)
  · obtain hn | rfl | hn := lt_trichotomy n a
    · have hz := CochainComplex.isZero_of_isStrictlyGE (P.truncGE a) a n hn
      exact ⟨ObjectProperty.flat_of_isZero hz, T.prop_of_isZero hz⟩
    · exact ⟨ObjectProperty.prop_of_iso _ (P.truncGEXIsoOpcycles n).symm hop,
        T.prop_of_iso (P.truncGEXIsoOpcycles n).symm hopT⟩
    · exact ⟨ObjectProperty.prop_of_iso _ (P.truncGEXIso a n hn).symm (hSf _ (hP n)),
        T.prop_of_iso (P.truncGEXIso a n hn).symm (hST _ (hP n))⟩

end DerivedCategory
