/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.HomColimitExtension
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.AlgebraicGeometry.CondensedLocalPieceCostalkModel
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
public import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeDerivedHom
public import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeHomContinuity
public import WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedPiece
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def

public import WeilConjectures.AlgebraicGeometry.CondensedConstructiblePiece
import WeilConjectures.AlgebraicGeometry.CondensedLfpHomContinuity
set_option linter.privateModule false

/-! # Filtered Hom continuity for one locally closed piece -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

noncomputable local instance
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] (X : Scheme.{u}) :
    HasZeroMorphisms (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) := inferInstance

local instance
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] (X : Scheme.{u}) {I : Type (u + 1)} [SmallCategory I]
    (N : I ⥤ CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ℤ) : HasColimit N := by
  let C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  have : HasColimitsOfShape I C := inferInstance
  have (n : ℤ) : HasColimit (N ⋙ HomologicalComplex.eval C (.up ℤ) n) :=
    HasColimitsOfShape.has_colimit _
  exact ⟨⟨⟨_, HomologicalComplex.isColimitCoconeOfHasColimitEval N⟩⟩⟩

private theorem comparison_isIso_of_compatible_iso
    {A : Type*} [Category A] {I : Type*} [Category I]
    {D E : I ⥤ A} [HasColimitsOfShape I A]
    (c : Cocone D) (d : Cocone E) (e : D ≅ E) (v : c.pt ≅ d.pt)
    (hleg : ∀ s : I, c.ι.app s ≫ v.hom = e.hom.app s ≫ d.ι.app s)
    (hd : IsIso (colimit.desc E d)) : IsIso (colimit.desc D c) := by
  have h : colimit.desc D c ≫ v.hom = colimMap e.hom ≫ colimit.desc E d := by
    apply colimit.hom_ext
    intro s
    simp only [colimit.ι_desc_assoc, ι_colimMap_assoc, colimit.ι_desc]
    exact hleg s
  have : IsIso (colimit.desc D c ≫ v.hom) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ v.hom

private theorem homColimitProperty_of_iso
    {A : Type*} [Category.{u + 1} A] [Preadditive A]
    [HasShift A ℤ]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ A) (c : Cocone D) {K S : A} (e : K ≅ S)
    (hS : homColimitProperty D c S) : homColimitProperty D c K := by
  intro n
  let eF := Functor.isoWhiskerLeft (shiftFunctor A n)
    (preadditiveCoyoneda.mapIso e.symm.op)
  apply (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.1
  obtain ⟨hc⟩ := (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.2 (hS n)
  exact ⟨IsColimit.mapCoconeEquiv eF.symm hc⟩

private theorem local_piece_continuity_of_local
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {Z U : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (j : U ⟶ Z) [IsOpenImmersion j] [QuasiCompact j]
    (P : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (N : I ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) ℤ)
    (hN : ∃ a : ℤ, ∀ (s : I) (r : ℤ), r < a → IsZero ((N.obj s).X r))
    (hP : ∀ (L : I ⥤ CochainComplex
        (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)) ℤ),
      (∃ a : ℤ, ∀ (s : I) (r : ℤ), r < a → IsZero ((L.obj s).X r)) →
      ∀ n : ℤ, IsIso (colimit.desc _
        ((condensedShiftedHom Λ U ((DerivedCategory.singleFunctor _ 0).obj P) n).mapCocone
          (colimit.cocone L)))) :
    homColimitProperty (N ⋙ DerivedCategory.Q)
      (DerivedCategory.Q.mapCocone (colimit.cocone N))
      ((DerivedCategory.singleFunctor _ 0).obj
        ((CondensedRing.lowerStar Λ i).obj
          ((CondensedRing.openImmersionLowerShriek Λ j).obj P))) := by
  intro n
  obtain ⟨L, hL, e, v, hleg⟩ := condensed_local_piece_costalk_model T Λ i j P N hN n
  exact comparison_isIso_of_compatible_iso (A := Ab.{u + 1}) (I := I) _
    ((condensedShiftedHom Λ U ((DerivedCategory.singleFunctor _ 0).obj P) n).mapCocone
      (colimit.cocone L)) e v hleg (hP L hL n)

private theorem locally_closed_generators_continuity
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (N : I ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) ℤ)
    (hN : ∃ a : ℤ, ∀ (s : I) (r : ℤ), r < a → IsZero ((N.obj s).X r))
    (hlocal : ∀ (U : Scheme.{u}) [TopologicalSpace.NoetherianSpace U]
      (P : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)),
      IsLocallyFinitelyPresented (condensedRingObj Λ U) P →
      ∀ (L : I ⥤ CochainComplex
        (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)) ℤ),
      (∃ a : ℤ, ∀ (s : I) (r : ℤ), r < a → IsZero ((L.obj s).X r)) →
      ∀ n : ℤ, IsIso (colimit.desc _
        ((condensedShiftedHom Λ U ((DerivedCategory.singleFunctor _ 0).obj P) n).mapCocone
          (colimit.cocone L))))
    : condensedLocallyClosedPiece Λ T ≤
      homColimitProperty (N ⋙ DerivedCategory.Q)
        (DerivedCategory.Q.mapCocone (colimit.cocone N)) := by
  intro K hK
  obtain ⟨Z, U, i, j, hi, hj, hqc, P, hP, ⟨eK⟩⟩ := hK
  let : IsClosedImmersion i := hi
  let : IsOpenImmersion j := hj
  let : QuasiCompact j := hqc
  let : TopologicalSpace.NoetherianSpace Z :=
    i.isClosedEmbedding.isEmbedding.isInducing.noetherianSpace
  let : TopologicalSpace.NoetherianSpace U :=
    j.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  have hp := local_piece_continuity_of_local (Z := Z) (U := U) (I := I)
    T Λ i j P N hN (hlocal U P hP)
  exact homColimitProperty_of_iso (I := I) (N ⋙ DerivedCategory.Q)
    (DerivedCategory.Q.mapCocone (colimit.cocone N)) eK hp

section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

/-- Extension by zero of a locally finitely presented condensed field module has
filtered derived Hom continuity on uniformly bounded below complexes.
Source: Hemo--Richarz--Scholbach, Lemma 5.3(2), locally free and costalk steps.
(blueprint: lem-weil-pbc-condensed-local-piece-hom-continuity)

Proof: write the piece as i_*j_!P[0], where i is closed and j is a quasi-compact open.
The noetherian closed subscheme and its open are qcqs. Local finite presentation over
these condensed finite field coefficients gives pro-etale local finite freeness.
The actual internal Hom functor Mod.ihom P preserves all small colimits by finite
free trivializations and joint conservativity of covering restrictions. Its right
adjunction gives exactness. The derived evaluation formula identifies Hom(P[0],L[n])
with the nth derived sections of termwise internal Hom. This termwise functor preserves
the common lower bound. Apply qcqs global sections continuity to the resulting diagram.
Transport the ringed-site module formulation to internal module objects with the same
coefficient ring and evaluation
pairing. The good-truncation cocone used by continuity maps termwise quasi-isomorphically
to the original cocone; exact filtered colimits preserve this comparison.
For the ambient diagram, adjunction identifies
Hom(i_*j_!P[0],N[n]) with Hom(P[0],j^*Ri^!N[n]). Recollement expresses i_*Ri^!N as
Cone(N → Rk_*k^*N)[-1] for the complementary quasi-compact open k. Qcqs pushforward
continuity and exact filtered colimits show that this cone commutes with the filtered
colimit. The same recollement gives the common lower bound for Ri^!N; exact j^*
also preserves it. Functorial bounded injective resolutions and good truncations give
strict uniformly bounded below diagrams representing these derived images and their
colimits. Include the bounded below derived categories in the ordinary derived categories
when applying adjunction. Apply the locally free calculation to j^*Ri^!N. Naturality of the
adjunction and of evaluation identifies every leg with the original cocone leg.
An isomorphism of the first argument transports the resulting isomorphism. -/
theorem condensed_local_piece_hom_continuity
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (N : I ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E.val) T)) ℤ)
    (hN : ∃ a : ℤ, ∀ (i : I) (r : ℤ), r < a → IsZero ((N.obj i).X r)) :
    condensedConstructiblePiece T ℓ E ≤
      homColimitProperty (N ⋙ DerivedCategory.Q)
        (DerivedCategory.Q.mapCocone (colimit.cocone N)) := by
  exact locally_closed_generators_continuity T (Profinite.continuousMapRingObj E.val) N hN
    (fun U _ P hP L hL n ↦ condensed_lfp_hom_continuity (I := I) U ℓ E P hP L hL n)

end

end AlgebraicGeometry.ProEtale
