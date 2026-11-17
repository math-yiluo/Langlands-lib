import Langlands.CommutativeAlgebra.StrictHenselianDvrExtension
import Langlands.GroupScheme.Reductive.StrictHenselianGenericIsoProof
import Langlands.GroupScheme.Reductive.FpqcLocalIsomorphismStatement
import Langlands.AbelianScheme.Tate.BaseChangeCoherence
import Langlands.GroupScheme.Reductive.SplitDataBaseChange

/-! # An actual fpqc isomorphism cover for a generically isomorphic DVR pair -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- An actual fpqc base change equipped with an actual group-scheme isomorphism. -/
structure FpqcGroupIsomorphismCover {S : Scheme.{u}} (G H : GroupScheme S) where
  base : Scheme.{u}
  map : base ⟶ S
  flat : Flat map
  surjective : Surjective map
  quasiCompact : QuasiCompact map
  iso : (baseChange map).obj G ≅ (baseChange map).obj H

namespace FpqcGroupIsomorphismCover

variable {S : Scheme.{u}} {G H : GroupScheme S}

/-- The corresponding singleton cover in the actual fpqc precoverage. -/
def cover (C : FpqcGroupIsomorphismCover G H) :
    Scheme.Cover.{u} Scheme.fpqcPrecoverage S where
  I₀ := PUnit
  X _ := C.base
  f _ := C.map
  mem₀ := by
    let := C.flat
    let := C.surjective
    let := C.quasiCompact
    change Presieve.ofArrows (fun _ : PUnit => C.base)
      (fun _ => C.map) ∈ _
    rw [Presieve.ofArrows_pUnit]
    exact C.map.singleton_mem_fpqcPrecoverage

/-- For reductive groups, the supplied fpqc-to-etale theorem turns this cover
into an actual etale cover with local isomorphisms. -/
theorem exists_etaleCover
    (h : ReductiveFpqcLocalIsomorphismStatement.{u})
    (C : FpqcGroupIsomorphismCover G H) (hG : IsReductive G) (hH : IsReductive H) :
    ∃ V : Scheme.Cover.{u} (Scheme.precoverage @Etale) S,
      ∀ j : V.I₀, Nonempty ((baseChange (V.f j)).obj G ≅
        (baseChange (V.f j)).obj H) :=
  h S G H hG hH ⟨C.cover, fun _ => ⟨C.iso⟩⟩

end FpqcGroupIsomorphismCover

section Dvr

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {G H : GroupScheme (Spec (CommRingCat.of R))}
    (hG : IsReductive G) (hH : IsReductive H)
    (f : (baseChange (Spec.algebraMap R K)).obj G ≅
      (baseChange (Spec.algebraMap R K)).obj H)

/-- A specified generic isomorphism of reductive DVR groups supplies an actual
fpqc cover on which the two groups are isomorphic, in the original universe. -/
def genericFpqcIsomorphismCover : FpqcGroupIsomorphismCover G H := by
  apply Classical.choice
  obtain ⟨A, _, _, _, _, _, _, hff⟩ :=
    Langlands.CommutativeAlgebra.strictHenselianDvrExtension R
  let := hff
  let L := FractionRing A
  have hinj : Function.Injective (algebraMap R L) :=
    FaithfulSMul.algebraMap_injective R L
  let i : K →+* L := IsFractionRing.lift (K := K) hinj
  let : Algebra K L := i.toAlgebra
  let : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq fun r => by
    exact (IsFractionRing.lift_algebraMap hinj r).symm
  let bA := Spec.algebraMap R A
  let cA := Spec.algebraMap A L
  let bK := Spec.algebraMap R K
  let cK := Spec.algebraMap K L
  have hc : cA ≫ bA = cK ≫ bK := by
    change algebraBaseMap A L ≫ algebraBaseMap R A =
      algebraBaseMap K L ≫ algebraBaseMap R K
    rw [splitTorus.algebraBaseMap_scalarTower, splitTorus.algebraBaseMap_scalarTower]
  let t (J : GroupScheme (Spec (CommRingCat.of R))) :
      (baseChange cA).obj ((baseChange bA).obj J) ≅
        (baseChange cK).obj ((baseChange bK).obj J) :=
    (baseChangeCompIso bA cA J).symm ≪≫
      eqToIso (congrArg (fun b => (baseChange b).obj J) hc) ≪≫
      baseChangeCompIso bK cK J
  let e := t G ≪≫ (baseChange cK).mapIso f ≪≫ (t H).symm
  obtain ⟨a⟩ := strictHenselianGenericIso A L
    ((baseChange bA).obj G) ((baseChange bA).obj H)
    (hG.baseChange bA) (hH.baseChange bA) ⟨e⟩
  have hb := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap R A))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr hff)
  exact ⟨⟨Spec (CommRingCat.of A), bA, hb.1, hb.2, inferInstance, a⟩⟩

end Dvr

end Langlands.GroupScheme
