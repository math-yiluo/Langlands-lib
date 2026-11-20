import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardOrbitSections
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitSectionCompactChange

/-! # Smoothness of the actual semistandard model comparison -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.Induction
open Langlands.HarmonicAnalysis.TorusFourier
open scoped CategoryTheory.MonObj

namespace Langlands.HarishChandraSchwartz.RationalSemistandard

universe u uV

variable {F : Type u} [Field F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G}
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalInducedT2 rationalInducedNonarchimedean

variable {p : SemistandardSpectralIndex i} (m n : LeviModel p)

local instance comparisonModelAffine : IsAffine m.scheme.X.left := by
  have := m.reductive.isAffineHom
  exact isAffine_of_isAffineHom m.scheme.X.hom

local instance comparisonModelTopology : TopologicalSpace (rationalPoints m.scheme) :=
  rationalPointTopology F m.scheme.X

local notation "Torus" m => (Fin (rationalImageRank (LeviModel.scheme m)) → Circle)

omit [LocallyOfFiniteType G.X.hom] in
/-- Each canonical coordinate is evaluation at a lift of a valuation basis
vector to the literal Levi subgroup. -/
private theorem exists_unitaryCoordinatePoint (j : Fin (rationalImageRank m.scheme)) :
    ∃ x : levi p, ∀ χ : unitaryUnramifiedCharacters m.normCharacters,
      (m.unitaryCoordinates χ j : ℂ) = (χ.val x : ℂ) := by
  obtain ⟨x, hx⟩ := rationalValuationImageProjection_surjective m.scheme
    ((rationalReductiveValuationBasis m.scheme m.reductive j).toMul)
  refine ⟨m.pointHomeomorph x, fun χ => ?_⟩
  let z := m.unitaryCoordinates χ
  have hχ := m.unitaryCoordinates.symm_apply_apply χ
  rw [← hχ]
  let := (rationalCharacterLattice F m.scheme m.reductive).2
  change (m.unitaryCoordinates (m.unitaryCoordinates.symm z) j : ℂ) =
    (rationalImageCharacterOfCoordinates m.scheme z
      (rationalValuationImageProjection m.scheme
        (m.pointHomeomorph.symm (m.pointHomeomorph x))) : ℂ)
  rw [m.unitaryCoordinates.apply_symm_apply, m.pointHomeomorph.symm_apply_apply, hx]
  exact congrArg (fun c : Circle => (c : ℂ))
    (rationalImageCharacterOfCoordinates_basis m.scheme z j).symm

/-- Use the published equality of actual characters to read the same
parameter in the other model's coordinates. -/
private def unitaryCoordinateChange (z : Torus n) : Torus m :=
  m.unitaryCoordinates (n.unitaryCharactersEquiv m (n.unitaryCoordinates.symm z))

private theorem unitaryCoordinateChange_eq_monomial :
    ∃ a : Fin (rationalImageRank m.scheme) → Fin (rationalImageRank n.scheme) → ℤ,
      unitaryCoordinateChange m n = finiteTorusMonomial a := by
  classical
  choose x hx using exists_unitaryCoordinatePoint m
  choose a ha using fun j => n.unitaryCoordinates_hasLaurent (x j)
  refine ⟨a, funext fun z => funext fun j => Circle.ext ?_⟩
  calc
    _ = ((n.unitaryCoordinates.symm z).val (x j) : ℂ) := hx j _
    _ = torusCharacter (a j) z := ha j z
    _ = ((finiteTorusMonomial a z) j : ℂ) := by
      rw [torusCharacter]
      exact (map_prod Circle.coeHom (fun k => z k ^ a j k) Finset.univ).symm

variable (d : CompactData p)
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p))

/-- Compact restriction at an actual character, before choosing its torus
coordinates. -/
private def compactOrbitValue (q : OrbitSections m π)
    (χ : unitaryUnramifiedCharacters m.normCharacters) :
    ProductInducedCompactPicture (decomposition p) d.compact π.obj :=
  haveI := (isClosed_parabolic p).locallyCompactSpace
  let psi := unitaryUnramifiedInclusion m.normCharacters χ
  productInducedCompactEquiv m.normCharacters (decomposition p) d.compact
    (isClosed_parabolic p) d.isCompact m.continuous_normCharacters d.projection_continuous
    (isClosed_radical p) d.factorization psi π.obj
    (q ⟨IrreducibleAdmissibleRep.twist psi.val.toMonoidHom
      (unramifiedCharacter_isOpen_ker m.normCharacters psi) π, χ, rfl⟩)

/-- Both reindexings keep the actual character and the twisted inducing
object, so the coefficient and its compact restriction agree. -/
private theorem compactOrbitValue_modelChange (q : OrbitSections m π)
    (χ : unitaryUnramifiedCharacters n.normCharacters) :
    compactOrbitValue n d π (m.orbitSectionsModelEquiv n π q) χ =
      compactOrbitValue m d π q (n.unitaryCharactersEquiv m χ) := rfl

set_option maxHeartbeats 600000 in
private theorem smoothOrbitSections_changeModel (q : OrbitSections m π)
    (hq : q ∈ smoothOrbitSections m d π) :
    m.orbitSectionsModelEquiv n π q ∈ smoothOrbitSections n d π := by
  refine ⟨(m.orbitSectionsModelEquiv_coherent_iff n π q).mpr hq.1, ?_⟩
  let f := fun z : Torus m => compactOrbitValue m d π q (m.unitaryCoordinates.symm z)
  have hf : f ∈ finiteSmoothFamilies _ _ := hq.2
  have heq : (fun z : Torus n => compactOrbitValue n d π
      (m.orbitSectionsModelEquiv n π q) (n.unitaryCoordinates.symm z)) =
      f ∘ unitaryCoordinateChange m n := by
    funext z
    change compactOrbitValue n d π (m.orbitSectionsModelEquiv n π q)
      (n.unitaryCoordinates.symm z) =
      compactOrbitValue m d π q
        (m.unitaryCoordinates.symm (m.unitaryCoordinates
          (n.unitaryCharactersEquiv m (n.unitaryCoordinates.symm z))))
    rw [m.unitaryCoordinates.symm_apply_apply]
    exact compactOrbitValue_modelChange m n d π q _
  obtain ⟨a, ha⟩ := unitaryCoordinateChange_eq_monomial m n
  change (fun z : Torus n => compactOrbitValue n d π
    (m.orbitSectionsModelEquiv n π q) (n.unitaryCoordinates.symm z)) ∈ finiteSmoothFamilies _ _
  rw [heq, ha]
  exact mem_finiteSmoothFamilies_comp_monomial hf a

private theorem smoothOrbitSections_changeCompact (e : CompactData p) :
    smoothOrbitSections m d π ≤ smoothOrbitSections m e π := by
  have := (isClosed_parabolic p).locallyCompactSpace
  exact productInducedSmoothOrbitSections_le_changeCompact (decomposition p) (isClosed_radical p)
    (isClosed_parabolic p) d.compact e.compact d.isCompact e.isCompact d.factorization
    e.factorization m.normCharacters π m.continuous_normCharacters d.projection_continuous
    m.unitaryCoordinates.toMulEquiv m.unitaryCoordinates_hasLaurent

/-- The prescribed actual model map preserves and reflects smoothness for
any two supplied compact pictures. -/
theorem modelSmoothComparison :
    ModelSmoothComparisonStatement.{u, uV} (F := F) (G := G) (i := i) := by
  intro p m n d e π q
  constructor
  · intro hq
    have h := smoothOrbitSections_changeModel n m e π _ hq
    rw [LeviModel.orbitSectionsModelEquiv_trans, LeviModel.orbitSectionsModelEquiv_refl] at h
    exact smoothOrbitSections_changeCompact m e π d h
  · intro hq
    exact smoothOrbitSections_changeCompact n d π e (smoothOrbitSections_changeModel m n d π q hq)

end Langlands.HarishChandraSchwartz.RationalSemistandard
