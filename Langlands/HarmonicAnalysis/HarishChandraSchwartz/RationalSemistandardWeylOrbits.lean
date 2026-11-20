import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardCoefficientFiber
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviDiscreteSeriesOrbitFiniteness
import Langlands.GroupScheme.Rational.SemistandardWeylTransporters
import Langlands.GroupScheme.RepresentedSubgroupTransport
import Langlands.Representation.Aubert.General.ConjugationComposition

/-! # Actual Weyl lift transport of the intrinsic semistandard orbits -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 650000

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.Induction

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.WeylOrbits

section OrbitTransport

variable {H : Type u} [Group H] [TopologicalSpace H] [NonarchimedeanGroup H]
  {M M' : Subgroup H} {I J : Type*}
  {ν : I → (M →* ℝ≥0ˣ)} {ν' : J → (M' →* ℝ≥0ˣ)}
  (e : M' ≃ₜ* M) (f : unitaryUnramifiedCharacters ν → unitaryUnramifiedCharacters ν')
  (hf : ∀ z x, (f z).val x = z.val (e x))
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := M))

omit [NonarchimedeanGroup H] in
private theorem classTwist_congr {a b : M' →* ℂˣ} (h : a = b)
    (ha : IsOpen (a.ker : Set M')) (hb : IsOpen (b.ker : Set M'))
    (C : SmoothDualClass.{0, u, uV} (k := ℂ) (G := M')) :
    SmoothDualClass.twist a ha C = SmoothDualClass.twist b hb C := by
  subst b
  rfl

/-- Pull back actual representatives when the displayed parameter map is
pullback by the very same topological group isomorphism. -/
def pullbackRepresentative (A : UnitaryOrbitRepresentative ν π) :
    UnitaryOrbitRepresentative ν' (IrreducibleAdmissibleRep.pullback e π) := by
  refine ⟨IrreducibleAdmissibleRep.pullback e A.val, ?_⟩
  obtain ⟨z, hz⟩ := A.property
  let a := unitaryUnramifiedInclusion ν z
  let b := unitaryUnramifiedInclusion ν' (f z)
  have h : b.val.toMonoidHom = a.val.toMonoidHom.comp e.toMonoidHom :=
    MonoidHom.ext (hf z)
  have hb := unramifiedCharacter_isOpen_ker ν' b
  have ha := unramifiedCharacter_isOpen_ker ν a
  have hbe : IsOpen ((a.val.toMonoidHom.comp e.toMonoidHom).ker : Set M') := h ▸ hb
  refine ⟨f z, ?_⟩
  exact (classTwist_congr h hb hbe _).trans
    ((SmoothDualClass.pullback_twist e a.val.toMonoidHom ha hbe (Quotient.mk _ π)).symm.trans
      (congrArg (SmoothDualClass.pullback e) hz))

end OrbitTransport

/-- An element in the target Levi changes actual conjugation by its
canonical inner inducing isomorphism. -/
private def leftInnerIso {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    {M L : Subgroup H} (n n' : H)
    (hn : ∀ x : H, x ∈ L ↔ n⁻¹ * x * n ∈ M)
    (hn' : ∀ x : H, x ∈ L ↔ n'⁻¹ * x * n' ∈ M)
    (m : L) (hm : (m : H) * n = n') (A : SmoothRep.{0, u, uV} ℂ M) :
    (conjugationFunctor n' hn').obj A ≅ (conjugationFunctor n hn).obj A := by
  subst n'
  exact (conjugationFunctorCompIsoApp n (m : H) hn (conjugationMembership_inner m) A).symm ≪≫
    conjugationFunctorInnerIso m ((conjugationFunctor n hn).obj A)

attribute [local instance]
  rationalWeightsIsAffine rationalWeightsTopology rationalWeightsTopologicalGroup
  rationalWeightsT2Field rationalWeightsLocallyCompact rationalWeightsMeasurableSpace
  rationalWeightsBorelSpace rationalInducedSecondCountable rationalInducedT2
  rationalInducedNonarchimedean

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ G} {p q : SemistandardSpectralIndex i}
  (hP : torusCentralizer i ≤ p.levi)
  (K : OpenSubgroup (rationalPoints G))

/-- A compact lift of an actual element in the relative Weyl equality
transporter. Its class is still taken in the published relative quotient. -/
abbrev CompactLift :=
  {n : normalizerPoints i // (n : rationalPoints G) ∈ K ∧
    (QuotientGroup.mk n : relativeWeylGroup i) ∈
      semistandardWeylConjugacySet i p.toLevi q.toLevi hP}

variable (n : CompactLift (p := p) (q := q) hP K)

/-- The genuine Weyl transporter value of the compact lift. -/
def weylElement : semistandardWeylConjugacySet i p.toLevi q.toLevi hP :=
  ⟨QuotientGroup.mk n.val, n.property.2⟩

/-- The corresponding rational point as an element of the actual compact. -/
def compactPoint : K := ⟨n.val, n.property.1⟩

set_option hygiene false in
local notation "g" => (n.val : rationalPoints G)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- The lift conjugates the source Levi into exactly the target Levi on all tests. -/
theorem conjugateLevi_eq : p.levi.comap (G.innerIso g).inv = q.levi :=
  (mk_mem_semistandardWeylConjugacySet_iff i p.toLevi q.toLevi hP n.val).mp n.property.2

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- The Levi anchor of the translated comparison has the intrinsic target Levi. -/
theorem conjugateAnchor_eq
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) (hχ : Dynamic.centralizer χ = p.levi) :
    Dynamic.centralizer (χ ≫ (G.innerIso g).hom) = q.levi := by
  have he : Dynamic.centralizer (χ ≫ (G.innerIso g).hom) =
      (Dynamic.centralizer χ).comap (G.innerIso g).inv := by
    simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      Dynamic.centralizer_eq_comap_of_iso (χ ≫ (G.innerIso g).hom) (G.innerIso g).symm
  exact he.trans ((congrArg (fun U => U.comap (G.innerIso g).inv) hχ).trans
    (conjugateLevi_eq hP K n))

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- The actual inverse-conjugation membership equivalence on the literal Levis. -/
theorem conjugationMembership (x : rationalPoints G) :
    x ∈ levi q ↔ g⁻¹ * x * g ∈ levi p := by
  change x ∈ q.levi.carrier (Over.mk (𝟙 _)) ↔ _
  rw [← conjugateLevi_eq hP K n]
  change (x ≫ (G.innerIso g).inv.hom.hom) ∈ levi p ↔ _
  rw [← G.innerIso_inv_hom, comp_innerIso_hom, constantPoint_self, inv_inv]

/-- The inducing object is pulled back by inverse conjugation of actual Levi points. -/
def leviPullback : levi q ≃ₜ* levi p := conjugationEquiv g (conjugationMembership hP K n)

variable (m : LeviModel p) (m' : LeviModel q)

local instance sourceAffine : IsAffine m.scheme.X.left :=
  have := m.reductive.isAffineHom
  isAffine_of_isAffineHom m.scheme.X.hom
local instance targetAffine : IsAffine m'.scheme.X.left :=
  have := m'.reductive.isAffineHom
  isAffine_of_isAffineHom m'.scheme.X.hom
local instance sourceTopology : TopologicalSpace (rationalPoints m.scheme) :=
  rationalPointTopology F m.scheme.X
local instance targetTopology : TopologicalSpace (rationalPoints m'.scheme) :=
  rationalPointTopology F m'.scheme.X

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
private theorem conjugateLevi_comap_eq : q.levi.comap (G.innerIso g).hom = p.levi := by
  rw [← conjugateLevi_eq hP K n, ← SubgroupFunctor.comap_comp, Iso.hom_inv_id,
    SubgroupFunctor.comap_id]

/-- Canonical conjugation between the actual representing Levi models. -/
def parameterIso : m.scheme ≅ m'.scheme :=
  SubgroupFunctor.IsRepresentedBy.isoOfComap m.represents m'.represents
    (G.innerIso g) (conjugateLevi_comap_eq hP K n)

/-- The inverse parameter-model map is literal inverse conjugation. -/
theorem pointHomeomorph_parameterIso_inv (x : rationalPoints m'.scheme) :
    m.pointHomeomorph (rationalPoints.map (parameterIso hP K n m m').inv x) =
      leviPullback hP K n (m'.pointHomeomorph x) := by
  apply Subtype.ext
  change (x ≫ (parameterIso hP K n m m').inv.hom.hom) ≫ m.inclusion.hom.hom =
    g⁻¹ * (x ≫ m'.inclusion.hom.hom) * g
  rw [parameterIso, SubgroupFunctor.IsRepresentedBy.isoOfComap_inv_points,
    ← G.innerIso_inv_hom, comp_innerIso_hom, constantPoint_self, inv_inv]

/-- The unitary character transport uses the actual rational norm algebras of
both represented Levis. -/
def conjugateCharacter : unitaryUnramifiedCharacters m.normCharacters →ₜ*
    unitaryUnramifiedCharacters m'.normCharacters :=
  (ContinuousMonoidHom.toContinuousMonoidHom
      (unitaryUnramifiedCharactersHomeomorph m'.pointHomeomorph
        (fun a => (rationalNormCharacters m'.scheme a).toMul))).comp
    ((rationalUnitaryUnramifiedCharacterRestrict (parameterIso hP K n m m').inv).comp
      (ContinuousMonoidHom.toContinuousMonoidHom
        (unitaryUnramifiedCharactersHomeomorph m.pointHomeomorph
          (fun a => (rationalNormCharacters m.scheme a).toMul)).symm))

/-- These characters are exactly pulled back along inverse conjugation of
literal Levi points. -/
theorem conjugateCharacter_apply (z : unitaryUnramifiedCharacters m.normCharacters) (x : levi q) :
    (conjugateCharacter hP K n m m' z).val x = z.val (leviPullback hP K n x) := by
  let y := m'.pointHomeomorph.symm x
  change z.val (m.pointHomeomorph (rationalPoints.map (parameterIso hP K n m m').inv y)) = _
  exact congrArg z.val ((pointHomeomorph_parameterIso_inv hP K n m m' y).trans
    (congrArg (leviPullback hP K n) (m'.pointHomeomorph.apply_symm_apply x)))

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p))

/-- The target inducing base object is the actual inverse-conjugation pullback. -/
abbrev conjugateBase := IrreducibleAdmissibleRep.pullback (leviPullback hP K n) π

/-- Every actual representative in the source orbit gives an actual
representative in its conjugate orbit. -/
def conjugateRepresentative (A : UnitaryOrbitRepresentative m.normCharacters π) :
    UnitaryOrbitRepresentative m'.normCharacters (conjugateBase hP K n π) :=
  pullbackRepresentative (leviPullback hP K n) (conjugateCharacter hP K n m m')
    (conjugateCharacter_apply hP K n m m') π A

variable (n' : CompactLift (p := p) (q := q) hP K)
  (hQ : torusCentralizer i ≤ q.levi)

include hQ in
omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- Two equal LEFT transporter classes differ on the left by a literal
point of the target Levi. -/
theorem left_difference_mem_levi
    (h : (weylElement hP K n').val * (weylElement hP K n).val⁻¹ ∈
      semistandardLeviRelativeWeylSubgroup i q.toLevi) :
    (n'.val : rationalPoints G) * g⁻¹ ∈ levi q := by
  have hw : (QuotientGroup.mk (n'.val * n.val⁻¹) : relativeWeylGroup i) ∈
      semistandardLeviRelativeWeylSubgroup i q.toLevi := by
    change QuotientGroup.mk' _ (n'.val * n.val⁻¹) ∈ _
    rw [map_mul, map_inv]
    exact h
  exact (mk_mem_semistandardLeviRelativeWeylSubgroup_iff i q.toLevi hQ _).mp hw

/-- Canonical change of the conjugate inducing object for a change of Weyl
lift by left multiplication in the target Levi. -/
def changeLiftInducingIso
    (h : (weylElement hP K n').val * (weylElement hP K n).val⁻¹ ∈
      semistandardLeviRelativeWeylSubgroup i q.toLevi)
    (A : SmoothRep.{0, u, uV} ℂ (levi p)) :
    (SmoothRep.pullback (leviPullback hP K n') A) ≅
      (SmoothRep.pullback (leviPullback hP K n) A) :=
  leftInnerIso g (n'.val : rationalPoints G) (conjugationMembership hP K n)
    (conjugationMembership hP K n')
    ⟨(n'.val : rationalPoints G) * g⁻¹, left_difference_mem_levi hP K n n' hQ h⟩
    (inv_mul_cancel_right (n'.val : rationalPoints G) g) A

end Langlands.HarishChandraSchwartz.RationalSemistandard.WeylOrbits
