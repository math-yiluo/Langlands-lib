import Langlands.GroupScheme.Reductive.AffineRegularBorel
import Langlands.GroupScheme.Dynamic.CentralizerFromResidueFibres

/-! # Relative centralizers of fibrewise regular coordinate cocharacters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AffineRegularBorel

variable {R : Type u} [CommRing R] {I J : Type u} [Fintype I]
    {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (n : I → ℤ)
    (P : RootDatum J (I → ℤ) (I → ℤ))
    (hP : IsFibrewiseRootDatumOf I G i P)
    (hn : ∀ a : J, ∑ j, P.root a j * n j ≠ 0)
    (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i)

include hP hn hG hmax in
/-- The centralizer equals the actual pulled-back torus on every field-valued fibre. -/
theorem centralizer_eq_range_field (k : Type u) [Field k] [Algebra R k] :
    Dynamic.centralizer (Dynamic.baseChangeCocharacter (algebraBaseMap R k)
        (cocharacter i n)) =
      SubgroupFunctor.range ((GroupScheme.baseChange (algebraBaseMap R k)).map i) := by
  let : Smooth G.X.hom := hG.smooth
  let F := GroupScheme.baseChange (algebraBaseMap R k)
  have hred : IsConnectedReductive (F.obj G) := hG.isConnectedReductive_algebraMap k
  let : IsAffineHom (F.obj G).X.hom := hred.isAffineHom
  have hreg : IsRegularCocharacter (splitTorus.baseChangeHom (K := k) G I i)
      (splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) I n) :=
    isRegular_field i n P hP hn k
  have hmaxk := splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise I G i hmax k
  rw [cocharacter_baseChange]
  calc
    _ = SubgroupFunctor.range (splitTorus.baseChangeHom (K := k) G I i) := by
      exact centralizer_comp_eq_range_of_isRegular (k := k) (G := F.obj G)
        (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
        hred (isSplitTorus_splitTorus I) (splitTorus.baseChangeHom (K := k) G I i) hmaxk
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) I n) hreg
    _ = _ := SubgroupFunctor.range_iso_comp
      (splitTorus.baseChangeIso (algebraBaseMap R k) I).symm _

include hP hn hG hmax in
/-- The same all-test comparison holds on every residue fibre of the original base. -/
theorem centralizer_eq_range_residue (s : Spec (CommRingCat.of R)) :
    Dynamic.centralizer (Dynamic.baseChangeCocharacter
        ((Spec (CommRingCat.of R)).fromSpecResidueField s) (cocharacter i n)) =
      SubgroupFunctor.range ((GroupScheme.baseChange
        ((Spec (CommRingCat.of R)).fromSpecResidueField s)).map i) := by
  let φ := Spec.preimage ((Spec (CommRingCat.of R)).fromSpecResidueField s)
  let : Algebra R ((Spec (CommRingCat.of R)).residueField s) := φ.hom.toAlgebra
  have hb : algebraBaseMap R ((Spec (CommRingCat.of R)).residueField s) =
      (Spec (CommRingCat.of R)).fromSpecResidueField s := Spec.map_preimage _
  have h := centralizer_eq_range_field i n P hP hn hG hmax
    ((Spec (CommRingCat.of R)).residueField s)
  rwa [hb] at h

variable [Mono i.hom.hom]

include hP hn hG hmax in
/-- A coordinate cocharacter regular on every fibre has the torus as its whole
dynamic centralizer over the original affine base. -/
theorem centralizer_eq_range_of_mono :
    Dynamic.centralizer (cocharacter i n) = SubgroupFunctor.range i := by
  let : Smooth G.X.hom := hG.smooth
  let : Smooth (splitTorus (Spec (CommRingCat.of R)) I).X.hom := smooth_splitTorus I
  exact Dynamic.centralizer_eq_range_of_residueFibres
    (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i
    (CommGroupScheme.groupHom
      (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I n))
    (centralizer_eq_range_residue i n P hP hn hG hmax)

/-- The coordinate torus is canonically isomorphic to any representative of
the dynamic centralizer of the fibrewise regular cocharacter. -/
def torusToCentralizerIso {C : GroupScheme (Spec (CommRingCat.of R))} {j : C ⟶ G}
    (hj : (Dynamic.centralizer (cocharacter i n)).IsRepresentedBy j) :
    splitTorus (Spec (CommRingCat.of R)) I ≅ C :=
  (show (Dynamic.centralizer (cocharacter i n)).IsRepresentedBy i from
    ⟨inferInstance, (centralizer_eq_range_of_mono i n P hP hn hG hmax).symm⟩).isoOfIsRepresentedBy hj

@[reassoc (attr := simp)]
theorem torusToCentralizerIso_hom_comp
    {C : GroupScheme (Spec (CommRingCat.of R))} {j : C ⟶ G}
    (hj : (Dynamic.centralizer (cocharacter i n)).IsRepresentedBy j) :
    (torusToCentralizerIso i n P hP hn hG hmax hj).hom ≫ j = i :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

end Langlands.GroupScheme.AffineRegularBorel
