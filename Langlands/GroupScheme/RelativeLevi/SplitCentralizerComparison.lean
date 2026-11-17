import Langlands.GroupScheme.Reductive.RelativeCentralizerRootDatum
import Langlands.GroupScheme.Reductive.RelativeCentralizerReductive
import Langlands.GroupScheme.Reductive.GlobalRootAnnihilatorCentrality
import Langlands.GroupScheme.Reductive.SplitBorelPositiveCoordinates
import Langlands.LinearAlgebra.RootDatumBaseExists
import Langlands.GroupScheme.CentralIsogeny.Basic

/-! # Actual centralizers depend only on the zero-root face -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

open LocalSplitCell Langlands.LinearAlgebra

namespace Dynamic

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- A central cocharacter has constant orbit on every scheme test. -/
theorem centralizer_eq_top_of_isCentral (χ : (Gm S).toGrp ⟶ G) (hχ : IsCentral χ) :
    centralizer χ = ⊤ := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  refine iff_of_true ?_ (Subgroup.mem_top _)
  change orbit χ x = _
  have hc : Commute (snd T (Gm S).X ≫ χ.hom.hom) (fst T (Gm S).X ≫ x) := by
    have h := hχ _ (snd T (Gm S).X) _ (𝟙 _) (fst T (Gm S).X ≫ x)
    simpa only [Category.id_comp] using h
  change (snd T (Gm S).X ≫ χ.hom.hom) * (fst T (Gm S).X ≫ x) *
    (snd T (Gm S).X ≫ χ.hom.hom)⁻¹ = fst T (Gm S).X ≫ x
  rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]

end Dynamic

namespace IsFibrewiseRootDatumOf

variable {R : Type u} [CommRing R] [Nontrivial R]
  {I J : Type u} [Fintype I]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  (hP : IsFibrewiseRootDatumOf I G i P)

include hP in
/-- Over a nontrivial base the actual full coordinate pairing is the ordinary
integer dot product, by any maximal-ideal field fibre. -/
theorem pairing_eq_coPairing (m n : I → ℤ) : P.toLinearMap m n = coPairing m n := by
  obtain ⟨a, ha⟩ := Ideal.exists_maximal R
  let : a.IsMaximal := ha
  let : Field (R ⧸ a) := Ideal.Quotient.field a
  exact hP.pairing (R ⧸ a) m n

end IsFibrewiseRootDatumOf

namespace splitTorus.RelativeCocharacterCentralizer

variable {R : Type u} [CommRing R] [Nontrivial R]
  {I J : Type u} [Fintype I] [DecidableEq I]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
  (P : RootDatum J (I → ℤ) (I → ℤ)) (hG : IsReductive G)
  (hmax : IsFibrewiseMaximalTorus (T := commGroupScheme _ I) i)
  (hP : IsFibrewiseRootDatumOf I G i P) (v v' : I → ℤ)
  (hzero : ∀ a, coPairing (P.root a) v = 0 → coPairing (P.root a) v' = 0)

/-- The second coordinate cocharacter, factored through the specified actual
centralizer of the first one by their common ambient torus. -/
def cocharacterInCentralizer : (Gm (Spec (CommRingCat.of R))).toGrp ⟶ groupScheme I G i v :=
  CommGroupScheme.groupHom (exponentCocharacter _ I v') ≫ torusHom I G i v

/-- The factored cocharacter retains its actual map into the ambient group. -/
theorem cocharacterInCentralizer_comp :
    cocharacterInCentralizer i v v' ≫ inclusion I G i v = cocharacter I G i v' := by
  rw [cocharacterInCentralizer, Category.assoc, torusHom_comp]
  rfl

include hG hmax hP hzero in
/-- A cocharacter annihilating the first cocharacter's zero roots is central in
its actual relative centralizer, on every scheme test. -/
theorem isCentral_cocharacterInCentralizer :
    IsCentral (cocharacterInCentralizer i v v') := by
  classical
  let : Smooth G.X.hom := hG.smooth
  let L := groupScheme I G i v
  let t := torusHom I G i v
  let Q := Langlands.LinearAlgebra.orthogonalRootPairing P v
  have hQL : IsFibrewiseRootDatumOf I L t Q := hP.coordinateCentralizer v
  let : Finite (orthogonalIndices P v) := hQL.finite
  let : Q.IsReduced := hQL.isReduced
  let b := RootDatumBase.base Q
  apply (isCentral_iff_range_le_center _).2
  intro Z x hx
  obtain ⟨s, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  let u := Gm.pointsEquiv _ Z s
  have hroots : RootCharactersOne Q (cocharPoint v' Z u) := by
    intro a
    have ha : coPairing (P.root a.val) v = 0 :=
      (hP.pairing_eq_coPairing (P.root a.val) v).symm.trans a.property
    change torusChar (P.root a.val) Z (cocharPoint v' Z u) = 1
    rw [torusChar_cocharPoint, hzero a.val ha, zpow_zero, Units.val_one]
  have hc := mem_center_of_rootCharacters_one (isReductive i v hG)
    (isFibrewiseMaximalTorus i v hmax) hQL b (cocharPoint v' Z u) hroots
  rw [cocharPoint_eq_comp, MulEquiv.symm_apply_apply] at hc
  exact hc

include hG hmax hP hzero in
/-- Inclusion of actual centralizer functors follows from the zero-root
containment, rather than being supplied as a premise. -/
theorem centralizer_le_of_zero_imp :
    Dynamic.centralizer (cocharacter I G i v) ≤ Dynamic.centralizer (cocharacter I G i v') := by
  intro T g hg
  rw [← (isRepresentedBy_inclusion I G i v).2] at hg
  obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hg
  have hx : x ∈ (Dynamic.centralizer (cocharacterInCentralizer i v v')).carrier T := by
    rw [Dynamic.centralizer_eq_top_of_isCentral _
      (isCentral_cocharacterInCentralizer i P hG hmax hP v v' hzero)]
    exact Subgroup.mem_top _
  have h := Dynamic.centralizer_le_comap (cocharacterInCentralizer i v v') (inclusion I G i v) T hx
  rw [SubgroupFunctor.mem_comap, cocharacterInCentralizer_comp] at h
  exact h

variable (hiff : ∀ a, coPairing (P.root a) v = 0 ↔ coPairing (P.root a) v' = 0)

include hG hmax hP hiff in
/-- Two coordinate cocharacters with the same zero roots have exactly the same
actual centralizer functor over the original nontrivial ring. -/
theorem centralizer_eq_of_zero_iff :
    Dynamic.centralizer (cocharacter I G i v) = Dynamic.centralizer (cocharacter I G i v') :=
  le_antisymm
    (centralizer_le_of_zero_imp i P hG hmax hP v v' (fun a => (hiff a).1))
    (centralizer_le_of_zero_imp i P hG hmax hP v' v (fun a => (hiff a).2))

/-- The actual ambient-compatible centralizer comparison isomorphism for the
common zero-root face. -/
def centralizerIsoOfZeroIff : groupScheme I G i v ≅ groupScheme I G i v' :=
  (isRepresentedBy_inclusion I G i v).isoOfIsRepresentedBy (show
    (Dynamic.centralizer (cocharacter I G i v)).IsRepresentedBy (inclusion I G i v') from by
      rw [centralizer_eq_of_zero_iff i P hG hmax hP v v' hiff]
      exact isRepresentedBy_inclusion I G i v')

/-- The actual comparison preserves the specified inclusions into G. -/
theorem centralizerIsoOfZeroIff_hom_comp :
    (centralizerIsoOfZeroIff i P hG hmax hP v v' hiff).hom ≫ inclusion I G i v' =
      inclusion I G i v :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

end splitTorus.RelativeCocharacterCentralizer

end Langlands.GroupScheme
