import Langlands.GroupScheme.RelativeLevi.ParabolicSourceGeometry
import Langlands.GroupScheme.RelativeLevi.Basic
import Langlands.GroupScheme.ClosedSubgroupMonomorphism
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.Rational.ParabolicConnectedConjugacy
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Dynamic.NormalizedLimits
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.HomScheme.PointedEtaleLifting
import Langlands.GroupScheme.HomScheme.FibreComparison
import Langlands.GroupScheme.Reductive.PinningScalarCoherence

/-! # Fibre geometry and pointed cocharacter lifting for relative parabolics -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G P : GroupScheme S} {i : P ⟶ G}

/-- A field parabolic is dynamic for a cocharacter already inside its source. -/
theorem IsParabolicSubgroup.exists_internal_dynamicCocharacter
    {k : Type u} [Field k] {G P : GroupScheme (Spec (CommRingCat.of k))}
    {i : P ⟶ G} (hi : IsParabolicSubgroup i) (hG : IsConnectedReductive G) :
    ∃ χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ P,
      (Dynamic.parabolic (χ ≫ i)).IsRepresentedBy i := by
  obtain ⟨χ, hχ⟩ :=
    ParabolicDynamicProof.exists_dynamicPresentation_of_isParabolicSubgroup hG i hi
  let : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  have hrep : (Dynamic.parabolic χ).IsRepresentedBy i := ⟨inferInstance, hχ⟩
  have hle : SubgroupFunctor.range χ ≤ Dynamic.parabolic χ :=
    (Dynamic.range_le_centralizer χ).trans (Dynamic.centralizer_le_parabolic χ)
  refine ⟨hrep.factorHom χ hle, ?_⟩
  rw [hrep.factorHom_comp]
  exact hrep

namespace HomScheme

/-- Lift a residue cocharacter and recover it through the actual pullback comparison. -/
theorem exists_pointed_etale_cocharacter
    {P : GroupScheme S} [Smooth P.X.hom] [IsAffineHom P.X.hom]
    (s : S)
    (χ₀ : (Gm (Spec (S.residueField s))).toGrp ⟶
      (baseChange (S.fromSpecResidueField s)).obj P) :
    ∃ (U : Scheme.{u}) (p : U ⟶ S)
      (b : Spec (S.residueField s) ⟶ U)
      (hb : b ≫ p = S.fromSpecResidueField s)
      (χ : (Gm U).toGrp ⟶ (baseChange p).obj P),
      Etale p ∧
        Dynamic.baseChangeCocharacter b χ ≫
          (Descent.pullbackComparison p b (S.fromSpecResidueField s) hb P).hom = χ₀ := by
  let c := S.fromSpecResidueField s
  let j₀ : RelativeHom (Gm S).toGrp P (Over.mk c) :=
    (Gm.baseChangeIso c).hom ≫ χ₀
  obtain ⟨U, p, b, hb, j, hp, hj⟩ :=
    splitSourcePointedEtaleLifting S (Gm S).toGrp P isSplitTorus_gm s j₀
  let χ : (Gm U).toGrp ⟶ (baseChange p).obj P :=
    (Gm.baseChangeIso p).inv ≫ j
  refine ⟨U, p, b, hb, χ, hp, ?_⟩
  have heval := evaluate_comparison (H := (Gm S).toGrp) (G := P)
    (show Over.mk c ⟶ Over.mk p from Over.homMk b hb) j
  rw [hj] at heval
  change (baseChange b).map j ≫
      (Descent.pullbackComparison p b c hb P).hom =
    (Descent.pullbackComparison p b c hb (Gm S).toGrp).hom ≫ j₀ at heval
  have hgm := Descent.gmBaseChange_tower p b c hb
  change Dynamic.baseChangeCocharacter b
    ((Gm.baseChangeIso p).inv ≫ j) ≫ _ = χ₀
  simp only [Dynamic.baseChangeCocharacter, Functor.map_comp, Category.assoc]
  rw [heval]
  change (Gm.baseChangeIso b).inv ≫
    (baseChange b).map (Gm.baseChangeIso p).inv ≫
      (Descent.pullbackComparison p b c hb (Gm S).toGrp).hom ≫
        (Gm.baseChangeIso c).hom ≫ χ₀ = χ₀
  rw [← Category.assoc _ (Gm.baseChangeIso c).hom, ← hgm]
  simp only [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
  simp

end HomScheme

/-- At each base point, lift an internal defining cocharacter to a pointed
etale neighbourhood, retaining the dynamic description on its specified fibre. -/
def RelativeParabolicPointedDynamicLiftingStatement : Prop :=
  ∀ (S : Scheme.{u}) (G P : GroupScheme S) (i : P ⟶ G),
    IsReductive G → IsRelativeParabolicSubgroup i → ∀ s : S,
      ∃ (U : Scheme.{u}) (p : U ⟶ S)
        (b : Spec (S.residueField s) ⟶ U)
        (_hb : b ≫ p = S.fromSpecResidueField s)
        (χ : (Gm U).toGrp ⟶ (baseChange p).obj P),
        Etale p ∧ IsClosedSubgroup ((baseChange b).map ((baseChange p).map i)) ∧
          (Dynamic.parabolic (Dynamic.baseChangeCocharacter b
            (χ ≫ (baseChange p).map i))).IsRepresentedBy
              ((baseChange b).map ((baseChange p).map i))

/-- Lift inside the parabolic source, then transport the exact dynamic fibre
identity through the source and ambient pullback comparisons. -/
theorem relativeParabolicPointedDynamicLifting :
    RelativeParabolicPointedDynamicLiftingStatement.{u} := by
  intro S G P i hG hi s
  let c := S.fromSpecResidueField s
  let i₀ := (baseChange c).map i
  obtain ⟨χ₀, hχ₀⟩ := (hi.residueFiber s).exists_internal_dynamicCocharacter
    (hG.isConnectedReductive_residueFiber s)
  let : Smooth P.X.hom := hi.smooth
  let : IsAffineHom P.X.hom := hi.isAffineHom
  obtain ⟨U, p, b, hb, χ, hp, hχ⟩ :=
    HomScheme.exists_pointed_etale_cocharacter (P := P) s χ₀
  let eP := Descent.pullbackComparison p b c hb P
  let eG := Descent.pullbackComparison p b c hb G
  let ip := (baseChange p).map i
  let ib := (baseChange b).map ip
  have hsquare : ib ≫ eG.hom = eP.hom ≫ i₀ :=
    Descent.pullbackComparison_naturality p b c hb i
  have hib : ib = eP.hom ≫ (i₀ ≫ eG.inv) := by
    rw [← Category.assoc, ← hsquare, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hc : IsClosedSubgroup ib := by
    rw [hib]
    exact ((hi.residueFiber s).isClosedSubgroup.comp_iso eG.symm).iso_comp eP
  have hcochar : Dynamic.baseChangeCocharacter b (χ ≫ ip) ≫ eG.hom = χ₀ ≫ i₀ := by
    change ((Gm.baseChangeIso b).inv ≫ (baseChange b).map (χ ≫ ip)) ≫ _ = _
    rw [Functor.map_comp, Category.assoc, Category.assoc, hsquare,
      ← Category.assoc, ← Category.assoc]
    exact congrArg (fun k => k ≫ i₀) hχ
  refine ⟨U, p, b, hb, χ, hp, hc, ?_⟩
  change (Dynamic.parabolic (Dynamic.baseChangeCocharacter b (χ ≫ ip))).IsRepresentedBy ib
  refine ⟨hc.mono_overHom, ?_⟩
  rw [hib, SubgroupFunctor.range_iso_comp]
  rw [Dynamic.parabolic_eq_comap_of_iso
    (Dynamic.baseChangeCocharacter b (χ ≫ ip)) eG, hcochar]
  exact (hχ₀.comp_iso eG.symm).2

end Langlands.GroupScheme
