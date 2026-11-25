/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ConstructibleTorsionCurveSheaf
public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Ring.ULift
import WeilConjectures.AlgebraicGeometry.Curve.DenseOpenHighCohomology
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.Data.Int.GCD

/-!
# DenseOpenVanishingComparison

Source: Stacks Project, Lemma 0GJA.
(blueprint: lem-pbc-j2-dense-open-vanishing-comparison).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

private noncomputable abbrev coefficientFunctor :=
  (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
    ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom

open CategoryTheory.Limits in
private noncomputable def coefficientKanIso (X Y : Scheme.{u})
    (L : X.Etaleᵒᵖ ⥤ Y.Etaleᵒᵖ) :
    (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙ L.lan ⋙
      presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ⋙
        sheafCompose Y.smallEtaleTopology coefficientFunctor ≅
    sheafCompose X.smallEtaleTopology coefficientFunctor ⋙
      sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) ⋙
        L.lan ⋙ presheafToSheaf Y.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) := by
  let E := coefficientFunctor.{u}
  have : E.IsEquivalence := inferInstance
  have : PreservesColimitsOfSize.{u + 2, u + 2} E := inferInstance
  have : Y.smallEtaleTopology.PreservesSheafification E :=
    GrothendieckTopology.instPreservesSheafification Y.smallEtaleTopology E
  let P := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let Q := presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}
  let R := presheafToSheaf Y.smallEtaleTopology
    (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
  let W := (Functor.whiskeringRight Y.Etaleᵒᵖ _ _).obj E
  have : E.PreservesLeftKanExtensions L := by
    intro F
    have : E.PreservesPointwiseLeftKanExtension F L := fun c ↦ by
      have : PreservesColimit (CostructuredArrow.proj L c ⋙ F) E :=
        (E.asEquivalence.toAdjunction.leftAdjoint_preservesColimits.preservesColimitsOfShape
          (J := CostructuredArrow L c)).preservesColimit
      exact Functor.preservesPointwiseLeftKanExtensionAtOfPreservesColimit E F L c
    exact Functor.preservesPointwiseLKEOfHasPointwiseAndPreservesPointwise E F L
  let e := sheafComposeNatIso Y.smallEtaleTopology E
    (sheafificationAdjunction _ _) (sheafificationAdjunction _ _)
  let e' := E.lanCompIsoOfPreserves L
  change (P ⋙ L.lan ⋙ Q) ⋙ sheafCompose _ E ≅ _
  refine (Functor.associator P (L.lan ⋙ Q) (sheafCompose _ E)) ≪≫ ?_
  refine Functor.isoWhiskerLeft P
    ((Functor.associator L.lan Q (sheafCompose _ E)) ≪≫
      Functor.isoWhiskerLeft L.lan e.symm ≪≫
      (Functor.associator L.lan W R).symm ≪≫
      Functor.isoWhiskerRight e' R) ≪≫ ?_
  exact Iso.refl _

open CategoryTheory.Limits in
private theorem primary_of_mono {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (ε : G ⟶ F) [Mono ε] (p : ℕ) (hF : Scheme.IsPrimaryTorsionSheaf Λ F p) :
    Scheme.IsPrimaryTorsionSheaf Λ G p := by
  have : LocallySmall.{u} X.Etale := locallySmall_self _
  have : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  have : AB5OfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    AB5OfSize_of_univLE.{u, u, u + 1, u + 1} _
  intro Ω _ _ s x
  let S : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤
      ModuleCat.{u + 1} Λ := (Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)
  have : PreservesFiniteLimits S := inferInstance
  obtain ⟨n, hn⟩ := hF Ω s (S.map ε x)
  refine ⟨n, (ModuleCat.mono_iff_injective (S.map ε)).mp (Functor.map_mono S ε) ?_⟩
  simpa only [map_nsmul, map_zero] using hn

open CategoryTheory.Limits in
private theorem invertible_of_mono {Λ : Type (u + 1)} [CommRing Λ] {X B : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (ε : G ⟶ F) [Mono ε] (hF : Scheme.IsTorsionSheafOfInvertibleOrder B F) :
    Scheme.IsTorsionSheafOfInvertibleOrder B G := by
  have : LocallySmall.{u} X.Etale := locallySmall_self _
  constructor
  have : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  have : AB5OfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    AB5OfSize_of_univLE.{u, u, u + 1, u + 1} _
  intro Ω _ _ s x
  let S : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤
      ModuleCat.{u + 1} Λ := (Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)
  have : PreservesFiniteLimits S := inferInstance
  obtain ⟨n, hn, hu, hx⟩ := hF.exists_isUnit_nsmul_eq_zero Ω s (S.map ε x)
  refine ⟨n, hn, hu,
    (ModuleCat.mono_iff_injective (S.map ε)).mp (Functor.map_mono S ε) ?_⟩
  simpa only [map_nsmul, map_zero] using hx

open CategoryTheory.Limits in
private theorem primary_invertible_isZero {Λ : Type (u + 1)} [CommRing Λ]
    {k : Type u} [Field k] {X : Scheme.{u}} (p : ℕ) [Fact p.Prime] [CharP k p]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hp : Scheme.IsPrimaryTorsionSheaf Λ F p)
    (hi : Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F) : IsZero F := by
  have : LocallySmall.{u} X.Etale := locallySmall_self _
  have : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  apply (IsZero.iff_id_eq_zero F).mpr
  apply Scheme.sheafHom_ext_of_sheafFiber_map_algClosurePoint
  intro s
  have := (Scheme.pointSmallEtale (X.algClosurePoint s)).sheafFiber_additive
    (A := ModuleCat.{u + 1} Λ)
  rw [CategoryTheory.Functor.map_id, Functor.map_zero]
  ext x
  obtain ⟨a, ha⟩ := hp _ (X.algClosurePoint s) x
  obtain ⟨n, _, hnunit, hn⟩ := hi.exists_isUnit_nsmul_eq_zero _ (X.algClosurePoint s) x
  let e := (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv
  have hnk : (n : k) ≠ 0 := by
    have hh : IsUnit (n : k) := by simpa using hnunit.map e.toMonoidHom
    exact hh.ne_zero
  have hndiv : ¬ p ∣ n := by
    rintro ⟨m, rfl⟩
    apply hnk
    simp [Nat.cast_mul]
  have hc := ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hndiv).pow_left a
  exact (nsmul_eq_zero_iff_of_coprime hc).mp ⟨ha, hn⟩

private noncomputable def cohomologyIsoEquiv {X : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (e : F ≅ G) (q : ℕ) :
    Sheaf.H F q ≃+ Sheaf.H G q where
  toFun := Sheaf.H.map e.hom q
  invFun := Sheaf.H.map e.inv q
  left_inv x := by rw [← Sheaf.H.map_comp_apply, e.hom_inv_id]; simp
  right_inv x := by rw [← Sheaf.H.map_comp_apply, e.inv_hom_id]; simp
  map_add' := map_add _

/-- Source: Stacks Project, Lemma 0GJA, proof, with Lemma 095L.
(blueprint: lem-pbc-j2-dense-open-vanishing-comparison).

Proof: The coefficient functor E is an equivalence, so it preserves colimits and
sheafification. Commuting E with the left Kan extensions defining inverse image and
extension by zero identifies G with the module-valued extension by zero of F. Apply
`dense_open_high_cohomology` to F, and compose its additive equivalences with the
cohomology equivalences induced by this identification. This proves the first clause.

The open-closed short exact sequence for the abelian sheaf P.F makes its dense-open
counit monic. Applying the left exact coefficient functor gives a monomorphism G -> F.
Geometric stalk functors preserve this monomorphism. If F is p-primary, apply primary
annihilation to the image of a stalk element of G and use injectivity to pull back the
annihilation. Thus F primary implies G primary. The high-degree equivalences then
transfer C3(G) to C3(F).

For the reverse implication, if F is primary for some characteristic prime r, uniqueness
of characteristic identifies r with the prime p in the C3(G) test. Apply C3(F) and
transfer subsingleton cohomology along the same equivalences. If instead F has
invertible-order torsion, the monomorphism makes G have invertible-order torsion too.
Every stalk element of a p-primary G is killed by p^a and by an integer n invertible
in k. Such n is not divisible by p, so p^a and n are coprime. Bezout makes the element
zero. Geometric stalk conservativity gives IsZero G, and its cohomology is zero.
The empty scheme, the full open, exponent a=0, and the zero sheaf are covered by the
same proofs. In characteristic zero there is no prime characteristic to test. Neither
the constructibility hypothesis nor the torsion of P.F is needed by this argument.
-/
theorem IsCurve.dense_open_vanishing_comparison {k : Type u} [Field k] [IsAlgClosed k]
    (P : CurveCoefficientPair k)
    (U : P.C.Opens) (hU : Dense (U : Set P.C)) :
    let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
      ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
    let F := (sheafCompose P.C.smallEtaleTopology E).obj P.F
    let F' := (Etale.openImmersionLowerShriek AddCommGrpCat.{u + 1} U.ι).obj
      ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj P.F)
    let G := (sheafCompose P.C.smallEtaleTopology E).obj F'
    (∀ q : ℕ, 1 < q → Nonempty
      (Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
        AddCommGrpCat.{u + 1})).obj G) q ≃+
       Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
        AddCommGrpCat.{u + 1})).obj F) q)) ∧
    (IsCurve.VanishingAboveOneOfIsPrimaryTorsionSheaf (ULift.{u + 1} ℤ) G k →
      IsCurve.VanishingAboveOneOfIsPrimaryTorsionSheaf (ULift.{u + 1} ℤ) F k) ∧
    ((Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F ∨
      ∃ p : ℕ, p.Prime ∧ CharP k p ∧
        Scheme.IsPrimaryTorsionSheaf (ULift.{u + 1} ℤ) F p) →
      IsCurve.VanishingAboveOneOfIsPrimaryTorsionSheaf (ULift.{u + 1} ℤ) F k →
      IsCurve.VanishingAboveOneOfIsPrimaryTorsionSheaf (ULift.{u + 1} ℤ) G k) := by
  classical
  dsimp only
  let E := coefficientFunctor.{u}
  let T := sheafCompose P.C.smallEtaleTopology E
  let F := T.obj P.F
  let B := (Etale.openImmersionLowerShriek AddCommGrpCat.{u + 1} U.ι).obj
    ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj P.F)
  let G := T.obj B
  let A := ModuleCat.{u + 1} (ULift.{u + 1} ℤ)
  let V := sheafCompose P.C.smallEtaleTopology (forget₂ A AddCommGrpCat.{u + 1})
  let JF := (Etale.openImmersionLowerShriek A U.ι).obj ((Etale.upperStar A U.ι).obj F)
  have : IsCurve P.toSpec := P.isCurve
  let eu : (sheafCompose U.toScheme.smallEtaleTopology E).obj
      ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj P.F) ≅
      (Etale.upperStar A U.ι).obj F :=
    (coefficientKanIso P.C U.toScheme
      (MorphismProperty.Over.pullback @Etale ⊤ U.ι).op).app P.F
  let ej : G ≅ JF :=
    (coefficientKanIso U.toScheme P.C
      (MorphismProperty.Over.map ⊤ (inferInstance : Etale U.ι)).op).app
        ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj P.F) ≪≫
      (Etale.openImmersionLowerShriek A U.ι).mapIso eu
  let ε := (Etale.openImmersionLowerShriekUpperStarAdjunction A U.ι).counit.app F
  have hhigh (q : ℕ) (hq : 1 < q) : Nonempty (Sheaf.H (V.obj G) q ≃+
      Sheaf.H (V.obj F) q) := by
    exact ⟨(cohomologyIsoEquiv (V.mapIso ej) q).trans
      (AddEquiv.ofBijective (Sheaf.H.map (V.map ε) q)
        ((IsCurve.dense_open_high_cohomology (ULift.{u + 1} ℤ) P.toSpec F U hU).1 q hq))⟩
  let εB := (Etale.openImmersionLowerShriekUpperStarAdjunction
    AddCommGrpCat.{u + 1} U.ι).counit.app P.F
  have hseq := Etale.shortExact_openClosedShortComplex AddCommGrpCat.{u + 1} U.ι
    U.closedComplement P.F (by rw [U.range_closedComplement, Scheme.Opens.range_ι])
  have : Mono εB := hseq.mono_f
  have : CategoryTheory.Limits.PreservesFiniteLimits T := by
    have : CategoryTheory.Limits.PreservesFiniteLimits (T ⋙ sheafToPresheaf _ _) :=
      inferInstanceAs (CategoryTheory.Limits.PreservesFiniteLimits (sheafToPresheaf _ _ ⋙
        (Functor.whiskeringRight _ _ _).obj E))
    exact CategoryTheory.Limits.preservesFiniteLimits_of_reflects_of_preserves T
      (sheafToPresheaf _ _)
  have : Mono (T.map εB) := inferInstance
  refine ⟨hhigh, ?_, ?_⟩
  · intro h p _ _ hp q hq
    obtain ⟨e⟩ := hhigh q hq
    have := h p (primary_of_mono (T.map εB) p hp) q hq
    exact e.symm.injective.subsingleton
  · intro ht h p hprime hchar hp q hq
    obtain ⟨e⟩ := hhigh q hq
    rcases ht with hi | ⟨r, hr, hc, hF⟩
    · have hz := primary_invertible_isZero p G hp
        (invertible_of_mono (T.map εB) hi)
      have : V.Additive := { map_add := by intros; rfl }
      exact Sheaf.subsingleton_H_of_isZero (V.map_isZero hz) q
    · have hrp : r = p := CharP.eq k hc hchar
      subst r
      have := h p hF q hq
      exact e.injective.subsingleton

end AlgebraicGeometry
