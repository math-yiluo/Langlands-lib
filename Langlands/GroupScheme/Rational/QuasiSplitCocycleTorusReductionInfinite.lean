import Langlands.GroupScheme.Rational.QuasiSplitCocycleTorusReductionStatement
import Langlands.GroupScheme.Rational.FiniteGaloisTwistExistenceStatement
import Langlands.GroupScheme.Rational.FiniteGaloisFormReductiveStatement
import Langlands.GroupScheme.Rational.InfiniteFieldStronglyRegularPointStatement
import Langlands.GroupScheme.Rational.QuasiSplitRegularConjugateStatement
import Langlands.GroupScheme.CentralIsogeny.StabilizerTorusStatement
import Langlands.GroupScheme.CentralIsogeny.QuasiSplitLiftStatement
import Langlands.GroupScheme.SimplyConnected.CoverExistenceStatement
import Langlands.GroupScheme.ActionDescent
import Langlands.GroupScheme.BaseChangeReflection

/-! # Conditional torus reduction of quasi-split semisimple cocycles over infinite fields -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Every morphism between spectra of fields is surjective, flat and quasi-compact. -/
theorem fieldSpecMorphism_fpqc {L L' : Type u} [Field L] [Field L']
    (f : Spec (CommRingCat.of L') ⟶ Spec (CommRingCat.of L)) :
    Surjective f ∧ Flat f ∧ QuasiCompact f := by
  obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = f := ⟨Spec.preimage f, Spec.map_preimage f⟩
  let : Algebra L L' := φ.hom.toAlgebra
  exact fieldExtension_fpqc L L'

namespace AutomorphicAction

variable {S : Scheme.{u}} {G A : GroupScheme S}

/-- A central actual kernel acts trivially in the conjugation action of a group on itself. -/
theorem conjugation_kernelActsTrivially_of_isCentral {π : G ⟶ A}
    (hπ : IsCentral (kernelι π)) :
    (conjugation (𝟙 G)).KernelActsTrivially π := by
  intro T k g
  have hc := commute_of_mem_center (hπ T k) g
  simp only [restrict_act, conjugation_act, Grp.id_hom_hom, Category.comp_id]
  rw [hc.eq, mul_inv_cancel_right]

end AutomorphicAction

namespace IsCentralIsogeny

variable {K : Type u} [Field K] {G A : GroupScheme (Spec (CommRingCat.of K))}
  {π : G ⟶ A}

/-- The conjugation action of `G` on itself, descended along a central isogeny `π`. -/
def innerAction (hπ : IsCentralIsogeny π) : AutomorphicAction A G :=
  letI := hπ.flat
  letI := hπ.surjective
  letI := hπ.isFinite
  (AutomorphicAction.conjugation (𝟙 G)).quotientAction π
    (AutomorphicAction.conjugation_kernelActsTrivially_of_isCentral hπ.isCentral_kernelι)

/-- The descended inner action of a lifted point is conjugation by the lift. -/
theorem innerAction_act_lift (hπ : IsCentralIsogeny π)
    {Z : Over (Spec (CommRingCat.of K))} (h g : Z ⟶ G.X) :
    hπ.innerAction.act (h ≫ π.hom.hom) g = h * g * h⁻¹ := by
  let := hπ.flat
  let := hπ.surjective
  let := hπ.isFinite
  exact ((AutomorphicAction.conjugation (𝟙 G)).quotientAction_act_lift π
    (AutomorphicAction.conjugation_kernelActsTrivially_of_isCentral
      hπ.isCentral_kernelι) h g).trans
    (by simp only [AutomorphicAction.conjugation_act, Grp.id_hom_hom, Category.comp_id])

end IsCentralIsogeny

/-- **Steinberg's torus reduction over infinite fields, conditionally.** Assuming the existence
of simply connected central covers, finite-Galois twisting, connected reductivity of
finite-Galois forms, strongly regular rational points over infinite fields, Steinberg's rational
conjugacy transfer for quasi-split simply connected groups, stabilizer tori through central
isogenies and lifting of quasi-splitness along central isogenies, every finite-Galois cocycle of
a quasi-split semisimple group over an infinite field has an actual torus reduction. -/
theorem quasiSplitCocycleTorusReduction_of_infinite
    (hcover : SimplyConnectedCoverExistenceStatement.{u})
    (htwist : FiniteGaloisTwistExistenceStatement.{u})
    (hform : FiniteGaloisFormConnectedReductiveStatement.{u})
    (hregular : InfiniteFieldStronglyRegularPointStatement.{u})
    (hconj : QuasiSplitSimplyConnectedRegularConjugateStatement.{u})
    (hstab : CentralIsogenyStabilizerTorusStatement.{u})
    (hlift : CentralIsogenyQuasiSplitLiftStatement.{u})
    (K : Type u) [Field K] [Infinite K]
    (G : GroupScheme (Spec (CommRingCat.of K))) (hG : IsSemisimple G) (hqs : IsQuasiSplit G)
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (ξ : Cocycle G (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))))) :
    Nonempty ξ.TorusReduction := by
  -- The simply connected central cover and the descended inner action on it.
  obtain ⟨C, π, hπ⟩ := hcover K G hG
  have hπc := hπ.isCentralIsogeny
  have hCred := hπ.isSimplyConnected.isSemisimple.isConnectedReductive
  let a := hπc.innerAction
  have hact : ∀ {Z : Over (Spec (CommRingCat.of K))} (h g : Z ⟶ C.X),
      a.act (h ≫ π.hom.hom) g = h * g * h⁻¹ := fun h g => hπc.innerAction_act_lift h g
  -- The inner twist `H` of the cover by `ξ`.
  obtain ⟨H, e, -, he⟩ := htwist K L G C hCred.isAffineHom a ξ
  have hHred := hform K L C H e hCred
  -- A strongly regular rational point of `H` and its transfer to the cover.
  obtain ⟨y, S, j, hS, hj, hy⟩ := hregular K H hHred
  have hCqs := hlift K C G π hπc hCred hqs
  obtain ⟨x, T, i, hT, hi, hx, L', _, _, _, _, r, g, hg⟩ :=
    hconj K L C G hπ.isSimplyConnected hCqs π hπc a hact ξ H e he y S j hS hj hy
  -- The stabilizer of `x` in `G` is contained in a closed torus.
  obtain ⟨T', j', hT', hj', hstab'⟩ := hstab K C G π hπc a hact x T i hT hi hx
  obtain ⟨hsurj, hflat, hqc⟩ := fieldSpecMorphism_fpqc r.left
  refine ⟨{
    carrier := L'
    refinement := r
    quasiCompact_refinement := hqc
    flat_refinement := hflat
    surjective_refinement := hsurj
    cochain := g ≫ π.hom.hom
    torus := T'
    isTorus := hT'
    inclusion := j'
    isClosedSubgroup := hj'
    factorization := ?_ }⟩
  intro Z b c
  apply hstab'
  -- The conjugates of `x` by the two pulled-back cochain values both map to `y`.
  have hpt : ∀ d : Z ⟶ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L'))),
      e.toFun (d ≫ r) ((d ≫ g) * (toUnit Z ≫ x) * (d ≫ g)⁻¹) = toUnit Z ≫ y := by
    intro d
    have h := congrArg (fun w => d ≫ w) hg
    simp only [← e.naturality, MonObj.comp_mul, GrpObj.comp_inv] at h
    simpa only [← Category.assoc, comp_toUnit] using h
  have hξ : a.act (ξ.toFun (b ≫ r) (c ≫ r)) ((c ≫ g) * (toUnit Z ≫ x) * (c ≫ g)⁻¹) =
      (b ≫ g) * (toUnit Z ≫ x) * (b ≫ g)⁻¹ := by
    apply (e.toFun (b ≫ r)).injective
    rw [he, hpt, hpt]
  rw [a.act_mul_left, a.act_mul_left, ← Category.assoc, ← Category.assoc, hact, hξ,
    ← GrpObj.inv_comp, hact]
  group
