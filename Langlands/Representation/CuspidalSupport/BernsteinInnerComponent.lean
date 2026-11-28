import Langlands.Representation.CuspidalSupport.BernsteinInnerInertia
import Langlands.Representation.CuspidalSupport.BernsteinComponentWeylGroup
import Langlands.Representation.CuspidalSupport.FiniteGroupInvariantFunctions
import Langlands.Representation.Plancherel.DynamicOppositeConjugationScalar

/-! # Component invariants inside a represented standard Levi -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe u v

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

attribute [local instance] canonicalTopology

namespace ComponentWeyl

variable {G H K : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]
  [IsAffine K.X.left] [LocallyOfFiniteType K.X.hom]

/-- Association of two unramified twists in the common ambient group. -/
abbrev TwistsAssociated (p : H ⟶ G) (q : K ⟶ G)
    (ρ : SmoothRep.{0, u, v} ℂ (rationalPoints H))
    (τ : SmoothRep.{0, u, v} ℂ (rationalPoints K)) (χ : UChar H) (ψ : UChar K) : Prop :=
  ∃ c : RationalLeviConjugacy p q,
    Nonempty (rationalUnramifiedTwist H χ ρ ≅
      rationalIsoPullback c.iso (rationalUnramifiedTwist K ψ τ))

/-- Regular functions invariant under the affine Weyl group of a cuspidal datum. -/
abbrev invariantAlgebra (p : H ⟶ G) (ρ : SmoothRep.{0, u, v} ℂ (rationalPoints H)) :=
  InvariantFunctions.fixedSubalgebra
    (unramifiedRegularFunctions (fun ψ => (rationalNormCharacters H ψ).toMul)) (weylGroup p ρ)

/-- Invariant regular functions are constant on associated twists. -/
theorem mem_invariantAlgebra_iff (p : H ⟶ G) (ρ : SmoothRep.{0, u, v} ℂ (rationalPoints H))
    (f : unramifiedRegularFunctions (fun ψ => (rationalNormCharacters H ψ).toMul)) :
    f ∈ invariantAlgebra p ρ ↔
      ∀ χ ψ, TwistsAssociated p p ρ ρ χ ψ → f.val χ = f.val ψ := by
  constructor
  · intro hf χ ψ h
    obtain ⟨w, hw, rfl⟩ := (assoc_iff_exists_weylGroup p ρ χ ψ).mp h
    exact hf w hw ψ
  · intro hf w hw ψ
    exact hf (w ψ) ψ ((assoc_iff_exists_weylGroup p ρ _ _).mpr ⟨w, hw, rfl⟩)

end ComponentWeyl

variable {G M : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffineHom M.X.hom]
  [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType M.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
  {ν : cocharacterLattice T} {J : Finset (SimpleRoot i ν)} {j : M ⟶ G}

attribute [local instance] ambientAffine standardLeviClosed standardLeviAffine
  BernsteinLeviPresentation.standardLeviFiniteType

open ComponentWeyl

namespace BernsteinLeviPresentation

variable (D : BernsteinLeviPresentation i ν J j) (family : BernsteinStandardFamily i ν)

private abbrev intrinsicLeviHom (K : Finset (SimpleRoot D.torus ν)) :=
  Standard.leviHom D.torus ν (rootSet D.torus ν K)

private abbrev ambientLeviHom (K : Finset (SimpleRoot D.torus ν)) :=
  Standard.leviHom i ν (rootSet i ν (leviIndex J (D.innerIndex family K)))

/-- The inclusion of the transported inducing Levi into the coarse Levi. -/
def relativeLeviHom (K : Finset (SimpleRoot D.torus ν)) :
    bernsteinLeviScheme i ν (leviIndex J (D.innerIndex family K)) ⟶ M :=
  (D.innerLeviIso family K).inv ≫ intrinsicLeviHom D K

omit [ValuativeRel F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType M.X.hom] in
/-- The relative inclusion factors the ambient standard inclusion. -/
theorem relativeLeviHom_comp (K : Finset (SimpleRoot D.torus ν)) :
    D.relativeLeviHom family K ≫ j = ambientLeviHom D family K := by
  unfold relativeLeviHom
  rw [Category.assoc, ← D.innerLeviIso_hom_comp family K, Iso.inv_hom_id_assoc]

omit [ValuativeRel F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType M.X.hom] in
private theorem exists_relativeConjugacy_iff (K : Finset (SimpleRoot D.torus ν))
    (P : (bernsteinLeviScheme i ν (leviIndex J (D.innerIndex family K)) ≅
      bernsteinLeviScheme i ν (leviIndex J (D.innerIndex family K))) → Prop) :
    (∃ c : RationalLeviConjugacy (D.relativeLeviHom family K) (D.relativeLeviHom family K),
      P c.iso) ↔
    ∃ c : RationalLeviConjugacy (ambientLeviHom D family K) (ambientLeviHom D family K),
      c.point ∈ levi i ν J ∧ P c.iso := by
  let q := D.relativeLeviHom family K
  let k := ambientLeviHom D family K
  have hq : q ≫ j = k := D.relativeLeviHom_comp family K
  constructor
  · rintro ⟨c, h⟩
    have hinter : (M.innerIso c.point).hom ≫ j =
        j ≫ (G.innerIso (rationalPoints.map j c.point)).hom :=
      innerIso_hom_comp j c.point
    have hc : k ≫ (G.innerIso (rationalPoints.map j c.point)).hom = c.iso.hom ≫ k := by
      rw [← hq, Category.assoc, ← hinter, ← Category.assoc, c.commutes, Category.assoc]
    refine ⟨⟨rationalPoints.map j c.point, c.iso, hc⟩, ?_, h⟩
    change rationalPoints.map j c.point ∈ levi i ν J
    rw [← D.points_apply_coe]
    exact (D.points c.point).property
  · rintro ⟨c, hc, h⟩
    let x := D.points.symm ⟨c.point, hc⟩
    have hx : rationalPoints.map j x = c.point := by
      rw [← D.points_apply_coe, D.points.apply_symm_apply]
    let : Mono j := (Grp.forget _).mono_of_mono_map D.represented.1
    refine ⟨⟨x, c.iso, ?_⟩, h⟩
    apply (cancel_mono j).mp
    change (q ≫ (M.innerIso x).hom) ≫ j = (c.iso.hom ≫ q) ≫ j
    have hinter : (M.innerIso x).hom ≫ j = j ≫ (G.innerIso (rationalPoints.map j x)).hom :=
      innerIso_hom_comp j x
    rw [Category.assoc, hinter, hx, ← Category.assoc, hq, c.commutes, Category.assoc, hq]

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  [LocallyCompactSpace (rationalPoints M)] [NonarchimedeanGroup (rationalPoints M)]
  (a : BernsteinCuspidalDatum.{u, v} D.torus ν (D.standardFamily family))

private abbrev transportedRep :
    SmoothRep.{0, u, v} ℂ (rationalPoints (bernsteinLeviScheme i ν
      (leviIndex J (D.innerIndex family a.roots)))) :=
  rationalIsoPullback (D.innerLeviIso family a.roots).symm a.representation

omit [LocallyOfFiniteType M.X.hom]
  [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)] in
/-- The relative permutations form a subgroup of the ambient component Weyl group. -/
theorem relativeWeyl_le :
    weylGroup (D.relativeLeviHom family a.roots) (transportedRep D family a) ≤
      weylGroup (ambientLeviHom D family a.roots) (transportedRep D family a) := by
  intro w hw
  obtain ⟨c, _, h⟩ := (D.exists_relativeConjugacy_iff family a.roots
    (fun t => ∃ χ ∈ twistSet (transportedRep D family a) t, w = affinePerm t χ)).mp hw
  exact ⟨c, h⟩

omit [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)] in
/-- After transport of characters, intrinsic association is exactly relative association. -/
theorem twistsAssociated_iff_relative (χ ψ : UChar (bernsteinLeviScheme D.torus ν a.roots)) :
    TwistsAssociated (intrinsicLeviHom D a.roots) (intrinsicLeviHom D a.roots)
      a.representation a.representation χ ψ ↔
      TwistsAssociated (D.relativeLeviHom family a.roots) (D.relativeLeviHom family a.roots)
        (transportedRep D family a) (transportedRep D family a)
        (rationalUnramifiedCharacterTransport (D.innerLeviIso family a.roots) χ)
        (rationalUnramifiedCharacterTransport (D.innerLeviIso family a.roots) ψ) := by
  let A := rationalUnramifiedTwist _ χ a.representation
  let B := rationalUnramifiedTwist _ ψ a.representation
  let e := D.innerLeviIso family a.roots
  let tχ := rationalIsoPullbackTwistIso e.symm χ a.representation
  let tψ := rationalIsoPullbackTwistIso e.symm ψ a.representation
  let A' := rationalUnramifiedTwist _ (rationalUnramifiedCharacterTransport e χ)
    (transportedRep D family a)
  let B' := rationalUnramifiedTwist _ (rationalUnramifiedCharacterTransport e ψ)
    (transportedRep D family a)
  refine (D.conjugatePullback_iff family A B).trans (Iff.trans ?_
    (D.exists_relativeConjugacy_iff family a.roots
      (fun c => Nonempty (A' ≅ rationalIsoPullback c B'))).symm)
  constructor
  · rintro ⟨c, hc, ⟨h⟩⟩
    exact ⟨c, hc, ⟨tχ.symm ≪≫ h ≪≫
      (SmoothRep.pullbackFunctor (rationalPointIso c.iso)).mapIso tψ⟩⟩
  · rintro ⟨c, hc, ⟨h⟩⟩
    exact ⟨c, hc, ⟨tχ ≪≫ h ≪≫
      (SmoothRep.pullbackFunctor (rationalPointIso c.iso)).mapIso tψ.symm⟩⟩

set_option synthInstance.maxHeartbeats 200000 in
/-- Transport of regular functions identifies the intrinsic component algebra with
invariants under the relative Weyl group on the ambient inducing Levi. -/
def relativeComponentEquiv : invariantAlgebra (intrinsicLeviHom D a.roots) a.representation ≃ₐ[ℂ]
    invariantAlgebra (D.relativeLeviHom family a.roots) (transportedRep D family a) := by
  let e := D.innerLeviIso family a.roots
  let S := invariantAlgebra (intrinsicLeviHom D a.roots) a.representation
  let R := invariantAlgebra (D.relativeLeviHom family a.roots) (transportedRep D family a)
  let transport := rationalUnramifiedRegularFunctionsEquiv e
  have hmap : S.map transport.toAlgHom = R := by
    apply SetLike.ext
    intro f
    rw [Subalgebra.mem_map]
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine (mem_invariantAlgebra_iff _ _ _).mpr (fun χ ψ h => ?_)
      let χ₀ := rationalUnramifiedCharacterRestrict e.hom χ
      let ψ₀ := rationalUnramifiedCharacterRestrict e.hom ψ
      have hassoc := (D.twistsAssociated_iff_relative family a χ₀ ψ₀).mpr (by
        rw [show rationalUnramifiedCharacterTransport e χ₀ = χ from
          rationalUnramifiedCharacterRestrict_transport e.symm χ,
          show rationalUnramifiedCharacterTransport e ψ₀ = ψ from
          rationalUnramifiedCharacterRestrict_transport e.symm ψ]
        exact h)
      exact (mem_invariantAlgebra_iff _ _ _).mp hg _ _ hassoc
    · intro hf
      refine ⟨transport.symm f, (mem_invariantAlgebra_iff _ _ _).mpr ?_,
        transport.apply_symm_apply f⟩
      intro χ ψ h
      exact (mem_invariantAlgebra_iff _ _ _).mp hf _ _
        ((D.twistsAssociated_iff_relative family a χ ψ).mp h)
  exact (transport.subalgebraMap S).trans (Subalgebra.equivOfEq _ _ hmap)

omit [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)] in
/-- Transport preserves evaluation at corresponding characters. -/
theorem relativeComponentEquiv_eval
    (f : invariantAlgebra (intrinsicLeviHom D a.roots) a.representation)
    (χ : UChar (bernsteinLeviScheme D.torus ν a.roots)) :
    (D.relativeComponentEquiv family a f).val.val
      (rationalUnramifiedCharacterTransport (D.innerLeviIso family a.roots) χ) = f.val.val χ :=
  rationalUnramifiedRegularFunctionsEquiv_val_transport (D.innerLeviIso family a.roots) f.val χ

end BernsteinLeviPresentation

/-- Intrinsic component algebras of a represented standard Levi are relative invariant algebras
on the ambient inducing Levis. -/
def BernsteinInnerComponentStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (G M : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffineHom M.X.hom]
    [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType M.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T) (family : BernsteinStandardFamily i ν)
    (J : Finset (SimpleRoot i ν)) (j : M ⟶ G) (D : BernsteinLeviPresentation i ν J j),
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      [LocallyCompactSpace (rationalPoints M)] [NonarchimedeanGroup (rationalPoints M)]
      (a : BernsteinCuspidalDatum.{u, v} D.torus ν (D.standardFamily family)),
      let b := (D.ambientDatum family a).val
      let e := D.innerLeviIso family a.roots
      let p := Standard.leviHom D.torus ν (rootSet D.torus ν a.roots)
      let k := Standard.leviHom i ν (rootSet i ν (leviIndex J (D.innerIndex family a.roots)))
      weylGroup (D.relativeLeviHom family a.roots) b.representation ≤ weylGroup k b.representation ∧
      ∃ E : invariantAlgebra p a.representation ≃ₐ[ℂ]
          invariantAlgebra (D.relativeLeviHom family a.roots) b.representation,
        ∀ f χ, (E f).val.val (rationalUnramifiedCharacterTransport e χ) = f.val.val χ

/-- The relative Weyl subgroup and the evaluation-preserving component equivalence. -/
theorem bernsteinInnerComponent : BernsteinInnerComponentStatement.{u, v} := by
  intro F _ _ _ _ G M _ _ _ _ T i ν family J j D _ _ _ _ a
  exact ⟨D.relativeWeyl_le family a, D.relativeComponentEquiv family a,
    D.relativeComponentEquiv_eval family a⟩

end Langlands.CuspidalSupport
