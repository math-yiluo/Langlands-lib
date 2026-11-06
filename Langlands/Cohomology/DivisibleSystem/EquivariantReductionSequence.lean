import Langlands.Cohomology.DivisibleSystem.DerivedReductionSequence
import Langlands.Cohomology.EquivariantDerivedSections
import Langlands.Cohomology.SmoothSheafCohomology
import Langlands.Cohomology.LeftExactHomology
import Langlands.Representation.Category.ExactInclusion

/-!
# Reduction sequences for equivariant derived sections of `ℓ`-divisible systems

Milne, *Étale Cohomology* (1980), Ch. V, §1, Lemma 1.11, printed p.165: for an `l`-adic sheaf
`F = (F_n)` with flat levels and all `H^r(X, F_n)` finite, there are exact sequences
`0 → H^r(X_et, F)^(l^n) → H^r(X_et, F_n) → H^{r+1}(X_et, F)_{l^n} → 0`, where
`H^r(X, F) = lim_n H^r(X, F_n)` (p.164). Harris, *Galois properties of cohomological automorphic
forms on GL(n)*, §2, p.304, (2.1), defines `ℓ`-divisible systems of étale sheaves in smooth
`ℤ/ℓ^m[S(ẽ)]`-modules; by Fact 1 bis and p.305 the groups `H^q_c(U(ẽ), ℤ/ℓ^m)` are finite smooth
`S(ẽ)`-modules, and Lemma 2.8 (p.306) identifies the cohomology of the limit complex with
`lim_m H^q_c(U(ẽ), ℤ/ℓ^m)`.

The published `DerivedReductionSequence` proves Milne's lemma for right derived functors with
values in modules. This module extends it to targets with a group action:

* `derivedAdicReductionSequence_shortExact_of_limitExact`: in any abelian target category with
  limits of inverse systems, the sequence is short exact once `lim` keeps exact the exact
  sequences of inverse systems whose first terms satisfy a property `P`, and every
  `R^q F(T m)` satisfies `P`;
* `limit_exact_of_finite_rep`, `derivedAdicReductionSequence_shortExact_rep`: the case of
  representations `Rep k G`, with `P` finiteness of the underlying module; limits of
  representations are computed on the underlying modules;
* `equivariantCompactReductionSequence`, `equivariantGlobalReductionSequence`: the sequences for
  the derived compact and global section representations of equivariant module sheaves
  (`EquivariantDerivedSections.compactDerived`, `EquivariantDerivedSections.globalDerived`);
* `SmoothSheafCohomology.compactDerivedToRepIso`, `smoothCompactReductionSequence`: for
  smooth equivariant sheaves, the sequence for compact sections with values in `Rep R G`,
  compared with the published `SmoothSheafCohomology.compactDerived` through the exact inclusion
  `SmoothRep.toRep`. The limits are taken in `Rep R G`, where the `ℓ`-adic limits of Harris
  live: a limit of smooth representations need not be smooth;
* `smoothInvariantCompactReductionSequence`: the sequence for invariant compact sections of
  smooth equivariant sheaves, with values in modules.

The proof of the general statement is that of the published
`derivedAdicReductionSequence_shortExact`, with the exactness of limits as a hypothesis. For
representations it comes from Worker 3's `MittagLefflerShortExactLimitStatement`, an explicit
hypothesis not proved here, applied to the underlying modules. The finiteness of the derived
sections in each level is an explicit hypothesis: Harris's Fact 1 bis is not formalized, nor is
his construction of the system or Lemma 2.8. The statements and proofs are ours.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' w'' u v u' v' u''

section RepLimit

variable {k : Type u'} [CommRing k] {G : Type u''} [Monoid G]

/-- The representation version of the published `limit_exact_of_finite`: for an exact sequence
`X₁ ⟶ X₂ ⟶ X₃` of inverse systems of representations whose first terms are finite, the limit
sequence is exact, given Worker 3's `MittagLefflerShortExactLimitStatement`. The forgetful functor
to modules preserves limits and reflects exactness. -/
lemma limit_exact_of_finite_rep (hML : MittagLefflerShortExactLimitStatement.{u', v'} k)
    {S : ShortComplex (ℕᵒᵖ ⥤ Rep.{v'} k G)} (hS : S.Exact)
    (hfin : ∀ m, Finite (S.X₁.obj m)) : (S.map lim).Exact := by
  let Φ := forget₂ (Rep.{v'} k G) (ModuleCat.{v'} k)
  have : PreservesLimitsOfSize.{0, 0} Φ := preservesSmallestLimits_of_preservesLimits Φ
  have hS' : (S.map ((Functor.whiskeringRight ℕᵒᵖ _ _).obj Φ)).Exact :=
    shortComplex_exact_of_evaluation fun m => (hS.map ((evaluation ℕᵒᵖ _).obj m)).map Φ
  have h := limit_exact_of_finite hML hS' hfin
  rw [← ShortComplex.exact_map_iff_of_faithful _ Φ]
  exact ShortComplex.exact_of_iso (S.mapNatIso (preservesLimitNatIso Φ)).symm h

end RepLimit

namespace SmoothSheafCohomology

open Langlands.Sheaf.Equivariant

variable (R : Type u) [CommRing R]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : Type u) [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
variable [HasStableNeighbourhoods G X]

/-- The right derived functors of compact sections of smooth sheaves, taken with values in
algebraic representations, are the published `compactDerived` followed by the inclusion
`SmoothRep.toRep`, which is exact. -/
def compactDerivedToRepIso (q : ℕ) :
    (smoothSheafCompactSections R G X ⋙ Langlands.SmoothRep.toRep.{u, u, u}).rightDerived q ≅
      compactDerived R G X q ⋙ Langlands.SmoothRep.toRep.{u, u, u} :=
  @asIso _ _ _ _ _ (LeftExactHomology.isIso_derivedNatTrans Langlands.SmoothRep.toRep.{u, u, u}
    (smoothSheafCompactSections R G X) q)

end SmoothSheafCohomology

namespace DivisibleSystem

section DerivedLimitExact

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [EnoughInjectives C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  [HasLimitsOfShape ℕᵒᵖ D]
variable (F : C ⥤ D) [F.Additive] {ℓ : ℕ} (T : DivisibleSystem C ℓ)

/-- `derivedAdicReductionSequence_shortExact` for any abelian target category with limits of
inverse systems: it suffices that `lim` keeps exact those exact sequences of inverse systems
whose first terms satisfy a property `P`, and that every `R^q F(T m)` satisfies `P`. -/
theorem derivedAdicReductionSequence_shortExact_of_limitExact (P : D → Prop)
    (hlim : ∀ S : ShortComplex (ℕᵒᵖ ⥤ D), S.Exact → (∀ m, P (S.X₁.obj m)) →
      (S.map lim).Exact)
    (r q : ℕ) (hfin : ∀ m, P ((F.rightDerived q).obj (T.obj m))) :
    (T.derivedAdicReductionSequence F r q).ShortExact := by
  let E₁ : ShortComplex (ℕᵒᵖ ⥤ D) :=
    ShortComplex.mk (T.derivedPowSMulNatTrans F r q) (T.derivedReductionNatTrans F r q) (by
      refine NatTrans.ext (funext fun m => ?_)
      rw [NatTrans.comp_app, NatTrans.app_zero]
      exact T.map_powSMulMap_comp_map_projection F rfl _ q)
  let E₂ : ShortComplex (ℕᵒᵖ ⥤ D) :=
    ShortComplex.mk (T.derivedReductionNatTrans F r q) (T.derivedReductionδNatTrans F r q) (by
      refine NatTrans.ext (funext fun m => ?_)
      rw [NatTrans.comp_app, NatTrans.app_zero]
      exact T.map_projection_comp_derivedReductionδ F rfl _ q)
  let E₃ : ShortComplex (ℕᵒᵖ ⥤ D) :=
    ShortComplex.mk (T.derivedReductionδNatTrans F r q) (T.derivedPowSMulNatTrans F r (q + 1))
      (by
        refine NatTrans.ext (funext fun m => ?_)
        rw [NatTrans.comp_app, NatTrans.app_zero]
        exact T.derivedReductionδ_comp_map_powSMulMap F rfl q)
  have h₁ : (E₁.map lim).Exact := hlim E₁
    (shortComplex_exact_of_evaluation fun m =>
      DerivedPlus.rightDerived_exact₂ F (T.powSMulShortComplex_shortExact (m := m.unop) rfl) q)
    fun m => hfin m.unop
  have h₂ : (E₂.map lim).Exact := hlim E₂
    (shortComplex_exact_of_evaluation fun m =>
      DerivedPlus.rightDerived_exact₃ F (T.powSMulShortComplex_shortExact (m := m.unop) rfl) q
        (q + 1) rfl)
    fun m => hfin (m.unop + r)
  have h₃ : (E₃.map lim).Exact := hlim E₃
    (shortComplex_exact_of_evaluation fun m =>
      DerivedPlus.rightDerived_exact₁ F (T.powSMulShortComplex_shortExact (m := m.unop) rfl) q
        (q + 1) rfl)
    fun _ => hfin r
  have p₁ : (ShortComplex.mk _ _ (T.powSMul_limit_comp_π_eq_zero F r q)).Exact :=
    ShortComplex.exact_of_iso (ShortComplex.isoMk (S₁ := E₁.map lim) (Iso.refl _)
      (levelShiftLimitIso (T.tower ⋙ F.rightDerived q) r) (constLimitIso _)
      ((T.limMap_derivedPowSMulNatTrans_comp_levelShiftLimitIso F r q).trans
        (Category.id_comp _).symm).symm
      (T.limMap_derivedReductionNatTrans_comp_constLimitIso F r q).symm) h₁
  have p₂ : (ShortComplex.mk _ _ (T.π_comp_derivedAdicδ F r q)).Exact :=
    ShortComplex.exact_of_iso (ShortComplex.isoMk (S₁ := E₂.map lim)
      (levelShiftLimitIso (T.tower ⋙ F.rightDerived q) r) (constLimitIso _) (Iso.refl _)
      (T.limMap_derivedReductionNatTrans_comp_constLimitIso F r q).symm
      ((Category.comp_id _).trans (T.limMap_derivedReductionδNatTrans F r q)).symm) h₂
  have p₃ : (ShortComplex.mk _ _ (T.derivedAdicδ_comp_powSMul F r q)).Exact :=
    ShortComplex.exact_of_iso (ShortComplex.isoMk (S₁ := E₃.map lim) (constLimitIso _)
      (Iso.refl _)
      (levelShiftLimitIso (T.tower ⋙ F.rightDerived (q + 1)) r)
      ((Category.comp_id _).trans (T.limMap_derivedReductionδNatTrans F r q)).symm
      ((T.limMap_derivedPowSMulNatTrans_comp_levelShiftLimitIso F r (q + 1)).trans
        (Category.id_comp _).symm).symm) h₃
  exact cokernelKernelShortComplex_shortExact p₁ p₂ p₃

end DerivedLimitExact

section Rep

variable {k : Type u''} [CommRing k] {G : Type w''} [Monoid G]
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [EnoughInjectives C] [HasDerivedCategory.{w'} (Rep.{v'} k G)]
variable (F : C ⥤ Rep.{v'} k G) [F.Additive] {ℓ : ℕ} (T : DivisibleSystem C ℓ)

/-- Milne, Ch. V, Lemma 1.11, for right derived functors with values in representations: if
every `R^q F(T m)` is finite, then `derivedAdicReductionSequence F r q`,
`0 ⟶ (lim_m R^q F(T m)) / ℓ ^ r ⟶ R^q F(T r) ⟶ (lim_m R^(q+1) F(T m))[ℓ ^ r] ⟶ 0`,
is short exact, given Worker 3's `MittagLefflerShortExactLimitStatement`. -/
theorem derivedAdicReductionSequence_shortExact_rep
    (hML : MittagLefflerShortExactLimitStatement.{u'', v'} k) (r q : ℕ)
    (hfin : ∀ m, Finite ((F.rightDerived q).obj (T.obj m))) :
    (T.derivedAdicReductionSequence F r q).ShortExact :=
  T.derivedAdicReductionSequence_shortExact_of_limitExact F (fun A => Finite A)
    (fun _ hS hfin => limit_exact_of_finite_rep hML hS hfin) r q hfin

end Rep

section Equivariant

open Langlands.Sheaf.Equivariant

variable (R : Type u) [CommRing R] (G : Type u) [Group G]
variable (X : Type u) [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
  [HasDerivedCategory.{w} (TopologicalSheaf G X (ModuleCat.{u} R))]
  [HasDerivedCategory.{w'} (Rep.{u} R G)]
variable {ℓ : ℕ} (T : DivisibleSystem (TopologicalSheaf G X (ModuleCat.{u} R)) ℓ)

/-- Milne, Ch. V, Lemma 1.11, for equivariant compactly supported cohomology: for an `ℓ`-divisible
system `T` of equivariant module sheaves, the sequence of representations
`0 ⟶ (lim_m H^q_c(T m)) / ℓ ^ r ⟶ H^q_c(T r) ⟶ (lim_m H^(q+1)_c(T m))[ℓ ^ r] ⟶ 0`, where
`H^q_c = EquivariantDerivedSections.compactDerived R G X q`. -/
def equivariantCompactReductionSequence (r q : ℕ) : ShortComplex (Rep.{u} R G) :=
  T.derivedAdicReductionSequence (CompactSections.functor R G X) r q

/-- The first term of `equivariantCompactReductionSequence`. -/
lemma equivariantCompactReductionSequence_X₁ (r q : ℕ) :
    (equivariantCompactReductionSequence R G X T r q).X₁ =
      cokernel (powSMul ℓ r
        (limit (T.tower ⋙ EquivariantDerivedSections.compactDerived R G X q))) :=
  rfl

/-- The middle term of `equivariantCompactReductionSequence`. -/
lemma equivariantCompactReductionSequence_X₂ (r q : ℕ) :
    (equivariantCompactReductionSequence R G X T r q).X₂ =
      (EquivariantDerivedSections.compactDerived R G X q).obj (T.obj r) :=
  rfl

/-- The last term of `equivariantCompactReductionSequence`. -/
lemma equivariantCompactReductionSequence_X₃ (r q : ℕ) :
    (equivariantCompactReductionSequence R G X T r q).X₃ =
      kernel (powSMul ℓ r
        (limit (T.tower ⋙ EquivariantDerivedSections.compactDerived R G X (q + 1)))) :=
  rfl

/-- `equivariantCompactReductionSequence` is short exact if every `H^q_c(T m)` is finite, given
Worker 3's `MittagLefflerShortExactLimitStatement`. -/
theorem equivariantCompactReductionSequence_shortExact
    (hML : MittagLefflerShortExactLimitStatement.{u, u} R) (r q : ℕ)
    (hfin : ∀ m, Finite ((EquivariantDerivedSections.compactDerived R G X q).obj (T.obj m))) :
    (equivariantCompactReductionSequence R G X T r q).ShortExact :=
  T.derivedAdicReductionSequence_shortExact_rep _ hML r q hfin

/-- Milne, Ch. V, Lemma 1.11, for equivariant cohomology: for an `ℓ`-divisible system `T` of
equivariant module sheaves, the sequence of representations
`0 ⟶ (lim_m H^q(T m)) / ℓ ^ r ⟶ H^q(T r) ⟶ (lim_m H^(q+1)(T m))[ℓ ^ r] ⟶ 0`, where
`H^q = EquivariantDerivedSections.globalDerived R G X q`. -/
def equivariantGlobalReductionSequence (r q : ℕ) : ShortComplex (Rep.{u} R G) :=
  T.derivedAdicReductionSequence (sectionRepresentation R G X) r q

/-- The first term of `equivariantGlobalReductionSequence`. -/
lemma equivariantGlobalReductionSequence_X₁ (r q : ℕ) :
    (equivariantGlobalReductionSequence R G X T r q).X₁ =
      cokernel (powSMul ℓ r
        (limit (T.tower ⋙ EquivariantDerivedSections.globalDerived R G X q))) :=
  rfl

/-- The middle term of `equivariantGlobalReductionSequence`. -/
lemma equivariantGlobalReductionSequence_X₂ (r q : ℕ) :
    (equivariantGlobalReductionSequence R G X T r q).X₂ =
      (EquivariantDerivedSections.globalDerived R G X q).obj (T.obj r) :=
  rfl

/-- The last term of `equivariantGlobalReductionSequence`. -/
lemma equivariantGlobalReductionSequence_X₃ (r q : ℕ) :
    (equivariantGlobalReductionSequence R G X T r q).X₃ =
      kernel (powSMul ℓ r
        (limit (T.tower ⋙ EquivariantDerivedSections.globalDerived R G X (q + 1)))) :=
  rfl

/-- `equivariantGlobalReductionSequence` is short exact if every `H^q(T m)` is finite, given
Worker 3's `MittagLefflerShortExactLimitStatement`. -/
theorem equivariantGlobalReductionSequence_shortExact
    (hML : MittagLefflerShortExactLimitStatement.{u, u} R) (r q : ℕ)
    (hfin : ∀ m, Finite ((EquivariantDerivedSections.globalDerived R G X q).obj (T.obj m))) :
    (equivariantGlobalReductionSequence R G X T r q).ShortExact :=
  T.derivedAdicReductionSequence_shortExact_rep _ hML r q hfin

end Equivariant

section Smooth

open Langlands.Sheaf.Equivariant

variable (R : Type u) [CommRing R]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : Type u) [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
  [HasStableNeighbourhoods G X]
  [HasDerivedCategory.{w} (SmoothTopologicalSheaf R G X)]
  [HasDerivedCategory.{w'} (Rep.{u} R G)]
variable {ℓ : ℕ} (T : SmoothSheafDivisibleSystem R G X ℓ)

/-- Milne, Ch. V, Lemma 1.11, for compactly supported cohomology of an `ℓ`-divisible system `T` of
smooth equivariant module sheaves (Harris, §2, (2.1)): the sequence of representations
`0 ⟶ (lim_m H^q_c(T m)) / ℓ ^ r ⟶ H^q_c(T r) ⟶ (lim_m H^(q+1)_c(T m))[ℓ ^ r] ⟶ 0` for the right
derived functors `H^q_c` of compact sections with values in `Rep R G`. The limits are taken in
`Rep R G`: a limit of smooth representations need not be smooth. By
`SmoothSheafCohomology.compactDerivedToRepIso`, `H^q_c` is the published
`SmoothSheafCohomology.compactDerived` followed by `SmoothRep.toRep`; see the isomorphisms
`smoothCompactReductionSequenceX₁Iso`, `smoothCompactReductionSequenceX₂Iso` and
`smoothCompactReductionSequenceX₃Iso`. -/
def smoothCompactReductionSequence (r q : ℕ) : ShortComplex (Rep.{u} R G) :=
  T.derivedAdicReductionSequence
    (smoothSheafCompactSections R G X ⋙ Langlands.SmoothRep.toRep.{u, u, u}) r q

/-- `lim_m H^q_c(T m)` in `Rep R G` for the derived functors of `smoothCompactReductionSequence`
is the limit of the published `SmoothSheafCohomology.compactDerived` regarded as
representations. -/
def smoothCompactLimitIso (q : ℕ) :
    limit (T.tower ⋙ (smoothSheafCompactSections R G X ⋙
      Langlands.SmoothRep.toRep.{u, u, u}).rightDerived q) ≅
      limit (T.tower ⋙ SmoothSheafCohomology.compactDerived R G X q ⋙
        Langlands.SmoothRep.toRep.{u, u, u}) :=
  lim.mapIso (Functor.isoWhiskerLeft T.tower (SmoothSheafCohomology.compactDerivedToRepIso R G X q))

/-- The first term of `smoothCompactReductionSequence`, in terms of the published
`SmoothSheafCohomology.compactDerived`. -/
def smoothCompactReductionSequenceX₁Iso (r q : ℕ) :
    (smoothCompactReductionSequence R G X T r q).X₁ ≅
      cokernel (powSMul ℓ r (limit (T.tower ⋙ SmoothSheafCohomology.compactDerived R G X q ⋙
        Langlands.SmoothRep.toRep.{u, u, u}))) :=
  cokernel.mapIso _ _ (smoothCompactLimitIso R G X T q) (smoothCompactLimitIso R G X T q)
    (comp_powSMul ℓ r _).symm

/-- The middle term of `smoothCompactReductionSequence`, in terms of the published
`SmoothSheafCohomology.compactDerived`. -/
def smoothCompactReductionSequenceX₂Iso (r q : ℕ) :
    (smoothCompactReductionSequence R G X T r q).X₂ ≅
      Langlands.SmoothRep.toRep.{u, u, u}.obj
        ((SmoothSheafCohomology.compactDerived R G X q).obj (T.obj r)) :=
  (SmoothSheafCohomology.compactDerivedToRepIso R G X q).app (T.obj r)

/-- The last term of `smoothCompactReductionSequence`, in terms of the published
`SmoothSheafCohomology.compactDerived`. -/
def smoothCompactReductionSequenceX₃Iso (r q : ℕ) :
    (smoothCompactReductionSequence R G X T r q).X₃ ≅
      kernel (powSMul ℓ r (limit (T.tower ⋙ SmoothSheafCohomology.compactDerived R G X (q + 1) ⋙
        Langlands.SmoothRep.toRep.{u, u, u}))) :=
  kernel.mapIso _ _ (smoothCompactLimitIso R G X T (q + 1)) (smoothCompactLimitIso R G X T (q + 1))
    (comp_powSMul ℓ r _).symm

/-- `smoothCompactReductionSequence` is short exact if every published
`SmoothSheafCohomology.compactDerived` of `T m` is finite (Harris's Fact 1 bis in his case, not
formalized here), given Worker 3's `MittagLefflerShortExactLimitStatement`. -/
theorem smoothCompactReductionSequence_shortExact
    (hML : MittagLefflerShortExactLimitStatement.{u, u} R) (r q : ℕ)
    (hfin : ∀ m, Finite ((SmoothSheafCohomology.compactDerived R G X q).obj (T.obj m))) :
    (smoothCompactReductionSequence R G X T r q).ShortExact :=
  T.derivedAdicReductionSequence_shortExact_rep _ hML r q fun m =>
    @Finite.of_equiv _ _ (hfin m) (Representation.equivOfIso
      ((SmoothSheafCohomology.compactDerivedToRepIso R G X q).app
        (T.obj m))).toLinearEquiv.toEquiv.symm

end Smooth

section SmoothInvariant

open Langlands.Sheaf.Equivariant

variable (R : Type u) [CommRing R]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : Type u) [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
  [HasStableNeighbourhoods G X]
  [HasDerivedCategory.{w} (SmoothTopologicalSheaf R G X)]
  [HasDerivedCategory.{w'} (ModuleCat.{u} R)]
variable {ℓ : ℕ} (T : SmoothSheafDivisibleSystem R G X ℓ)

/-- Milne, Ch. V, Lemma 1.11, for derived invariant compact sections of an `ℓ`-divisible system `T`
of smooth equivariant module sheaves: the sequence of modules
`0 ⟶ (lim_m H^q(T m)) / ℓ ^ r ⟶ H^q(T r) ⟶ (lim_m H^(q+1)(T m))[ℓ ^ r] ⟶ 0`, where
`H^q = SmoothSheafCohomology.invariantCompactDerived R G X q`. -/
def smoothInvariantCompactReductionSequence (r q : ℕ) : ShortComplex (ModuleCat.{u} R) :=
  T.derivedAdicReductionSequence (SmoothSheafCohomology.invariantCompactSections R G X) r q

/-- The first term of `smoothInvariantCompactReductionSequence`. -/
lemma smoothInvariantCompactReductionSequence_X₁ (r q : ℕ) :
    (smoothInvariantCompactReductionSequence R G X T r q).X₁ =
      cokernel (powSMul ℓ r
        (limit (T.tower ⋙ SmoothSheafCohomology.invariantCompactDerived R G X q))) :=
  rfl

/-- The middle term of `smoothInvariantCompactReductionSequence`. -/
lemma smoothInvariantCompactReductionSequence_X₂ (r q : ℕ) :
    (smoothInvariantCompactReductionSequence R G X T r q).X₂ =
      (SmoothSheafCohomology.invariantCompactDerived R G X q).obj (T.obj r) :=
  rfl

/-- The last term of `smoothInvariantCompactReductionSequence`. -/
lemma smoothInvariantCompactReductionSequence_X₃ (r q : ℕ) :
    (smoothInvariantCompactReductionSequence R G X T r q).X₃ =
      kernel (powSMul ℓ r
        (limit (T.tower ⋙ SmoothSheafCohomology.invariantCompactDerived R G X (q + 1)))) :=
  rfl

/-- `smoothInvariantCompactReductionSequence` is short exact if every `H^q(T m)` is finite, given
Worker 3's `MittagLefflerShortExactLimitStatement`. -/
theorem smoothInvariantCompactReductionSequence_shortExact
    (hML : MittagLefflerShortExactLimitStatement.{u, u} R) (r q : ℕ)
    (hfin : ∀ m, Finite ((SmoothSheafCohomology.invariantCompactDerived R G X q).obj
      (T.obj m))) :
    (smoothInvariantCompactReductionSequence R G X T r q).ShortExact :=
  T.derivedAdicReductionSequence_shortExact _ hML r q hfin

end SmoothInvariant

end DivisibleSystem

end Langlands.Cohomology
