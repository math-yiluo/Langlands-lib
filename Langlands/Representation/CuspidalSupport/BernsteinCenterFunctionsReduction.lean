import Langlands.Representation.CuspidalSupport.BernsteinCenterFunctionsBasics
import Langlands.Representation.CuspidalSupport.BernsteinDecompositionStatements
import Langlands.Representation.Category.DecompositionCenterAssembly

/-! # Renard VI.10.4, Theorem (second sentence) with Remark 1, from the first sentence

The centre `ℨ(G)` of the category of smooth representations is identified with the algebra of
functions on `Ω(G)` that are polynomial on every component, assuming the first sentence of the
Theorem (the centre of each block `M(G)_Ω` is the algebra of polynomial functions on `Ω`,
published as `BernsteinBlockCenterFunctionsStatement`), the Bernstein decomposition (VI.7.2,
`BernsteinDecompositionStatement`) and the invariance of the irreducible subquotients of the
inductions under association (VI.5.4, `BernsteinAssociatedSupportInvarianceStatement`).

The unconditional ingredients proved here are: the saturated block is closed under
subquotients; an inertial relation `a₀ ~ a` transports every twist `(M_a, ρ_a ⊗ ω)` to an
associated twist `(M_{a₀}, ρ_{a₀} ⊗ ω₀)`; associated twisted data are associated cuspidal data,
so (under VI.5.4) their inductions share an irreducible subquotient, on which the scalars of a
central element on the two inductions must agree.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

section Helpers

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance instCenterFunctionsReductionAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance instCenterFunctionsReductionTopology :
    TopologicalSpace (rationalPoints G) := pointTopology
local instance instCenterFunctionsReductionLeviClosedImmersion
    (I : Finset (SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance instCenterFunctionsReductionLeviAffine (I : Finset (SimpleRoot i ν)) :
    IsAffine (bernsteinLeviScheme i ν I).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance instCenterFunctionsReductionLeviFiniteType
    (I : Finset (SimpleRoot i ν)) :
    LocallyOfFiniteType (bernsteinLeviScheme i ν I).X.hom := by
  rw [← (Standard.leviHom i ν (rootSet i ν I)).hom.hom.w]
  infer_instance
local instance instCenterFunctionsReductionLeviTopology (I : Finset (SimpleRoot i ν)) :
    TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν I)) :=
  rationalPointTopology F (bernsteinLeviScheme i ν I).X

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

/-- The saturated Bernstein block is closed under subquotients. -/
theorem bernsteinSaturatedBlockProperty_of_isSubquotient
    {s : BernsteinInertialClass.{uF, max uF uV} i ν family}
    {V W : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)}
    (hV : bernsteinSaturatedBlockProperty i ν family s V) (hWV : SmoothRep.IsSubquotient W V) :
    bernsteinSaturatedBlockProperty i ν family s W :=
  (bernsteinBlockProperty_iff_saturated s W).mp
    (bernsteinBlockProperty_of_isSubquotient
      ((bernsteinBlockProperty_iff_saturated s V).mpr hV) hWV)

/-- Every inertial class is the class of some cuspidal datum. -/
theorem exists_bernsteinInertialClass_eq (s : BernsteinInertialClass.{uF, uV} i ν family) :
    ∃ a : BernsteinCuspidalDatum.{uF, uV} i ν family, bernsteinInertialClass i ν family a = s :=
  Quotient.exists_rep s

/-- Every `i_P^G(ρ ⊗ ω)`, `ω ∈ X(M)`, is nonzero. -/
theorem nontrivial_twistInduction (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (ω : unramifiedCharacters
      (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul)) :
    Nontrivial ((normalizedInductionFunctor (family.decomposition a.roots)
        (family.closedUnipotent a.roots)).obj
          (bernsteinLiteralLeviRep i ν a.roots
            (rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation))) := by
  have h := nontrivial_bernsteinInduction i ν family (a.unramifiedTwist i ν family ω)
  rw [bernsteinInduction_unramifiedTwist] at h
  exact h

/-- Twist transport: if `(M_{a₀}, ρ_{a₀})` and `(M_a, ρ_a)` are inertially equivalent, every
twist `(M_a, ρ_a ⊗ ω)` is associated to some twist `(M_{a₀}, ρ_{a₀} ⊗ ω₀)`. -/
theorem exists_twist_association (a₀ a : BernsteinCuspidalDatum.{uF, uV} i ν family)
    (h : IsBernsteinInertiaRelated i ν family a₀ a)
    (ω : unramifiedCharacters
      (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul)) :
    ∃ ω₀ : unramifiedCharacters
        (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a₀.roots) χ).toMul),
      ∃ c : RationalLeviConjugacy (Standard.leviHom i ν (rootSet i ν a₀.roots))
          (Standard.leviHom i ν (rootSet i ν a.roots)),
        Nonempty (rationalUnramifiedTwist (bernsteinLeviScheme i ν a₀.roots) ω₀ a₀.representation ≅
          rationalIsoPullback c.iso
            (rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation)) := by
  obtain ⟨c, χ, ⟨e⟩⟩ := h
  refine ⟨rationalUnramifiedCharacterRestrict c.iso.hom ω * χ, c, ⟨?_⟩⟩
  exact (rationalIsoPullbackTwistIso c.iso ω a.representation ≪≫
    SmoothRep.twistIso _ _ e ≪≫ rationalUnramifiedTwistMulIso _ _ _ _).symm

/-- Associated twists give associated (twisted) cuspidal data. -/
theorem areAssociated_unramifiedTwist (a b : BernsteinCuspidalDatum.{uF, uV} i ν family)
    (ω : unramifiedCharacters
      (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul))
    (ω' : unramifiedCharacters
      (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν b.roots) χ).toMul))
    (h : ∃ c : RationalLeviConjugacy (Standard.leviHom i ν (rootSet i ν a.roots))
        (Standard.leviHom i ν (rootSet i ν b.roots)),
      Nonempty (rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation ≅
        rationalIsoPullback c.iso
          (rationalUnramifiedTwist (bernsteinLeviScheme i ν b.roots) ω' b.representation))) :
    AreBernsteinCuspidalDataAssociated i ν family (a.unramifiedTwist i ν family ω)
      (b.unramifiedTwist i ν family ω') := by
  dsimp only [AreBernsteinCuspidalDataAssociated, BernsteinCuspidalDatum.unramifiedTwist,
    BernsteinCuspidalDatum.replaceInertia]
  obtain ⟨c, ⟨e⟩⟩ := h
  exact ⟨c, ⟨e⟩⟩

/-- Under VI.5.4, the inductions of associated twists share an irreducible subquotient. -/
theorem exists_common_irreducible_subquotient
    (hI : BernsteinAssociatedSupportInvarianceStatement.{uF, uV} i ν family)
    (a b : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (ω : unramifiedCharacters
      (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul))
    (ω' : unramifiedCharacters
      (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν b.roots) χ).toMul))
    (h : ∃ c : RationalLeviConjugacy (Standard.leviHom i ν (rootSet i ν a.roots))
        (Standard.leviHom i ν (rootSet i ν b.roots)),
      Nonempty (rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation ≅
        rationalIsoPullback c.iso
          (rationalUnramifiedTwist (bernsteinLeviScheme i ν b.roots) ω' b.representation))) :
    ∃ π : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G), π.IsIrreducible ∧
      SmoothRep.IsSubquotient π ((normalizedInductionFunctor (family.decomposition a.roots)
        (family.closedUnipotent a.roots)).obj
          (bernsteinLiteralLeviRep i ν a.roots
            (rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation))) ∧
      SmoothRep.IsSubquotient π ((normalizedInductionFunctor (family.decomposition b.roots)
        (family.closedUnipotent b.roots)).obj
          (bernsteinLiteralLeviRep i ν b.roots
            (rationalUnramifiedTwist (bernsteinLeviScheme i ν b.roots) ω' b.representation))) := by
  have hab := areAssociated_unramifiedTwist i ν family a b ω ω' h
  have hne := nontrivial_bernsteinInduction i ν family (a.unramifiedTwist i ν family ω)
  obtain ⟨π, hπ, hπa⟩ := SmoothRep.exists_isIrreducible_isSubquotient_of_nontrivial
    (bernsteinInduction i ν family (a.unramifiedTwist i ν family ω))
  have hπb := ((hI _ _ hab π).mp ⟨hπ, hπa⟩).2
  rw [bernsteinInduction_unramifiedTwist] at hπa hπb
  exact ⟨π, hπ, hπa, hπb⟩

/-- Under VI.5.4, an element of the centre acts by the same scalar on the inductions of two
associated twists (when it acts by scalars on both). -/
theorem scalar_eq_of_twistAssociated
    (hI : BernsteinAssociatedSupportInvarianceStatement.{uF, uV} i ν family)
    (z : CatCenter (SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)))
    (a b : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (ω : unramifiedCharacters
      (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul))
    (ω' : unramifiedCharacters
      (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν b.roots) χ).toMul))
    (h : ∃ c : RationalLeviConjugacy (Standard.leviHom i ν (rootSet i ν a.roots))
        (Standard.leviHom i ν (rootSet i ν b.roots)),
      Nonempty (rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation ≅
        rationalIsoPullback c.iso
          (rationalUnramifiedTwist (bernsteinLeviScheme i ν b.roots) ω' b.representation)))
    {p q : ℂ}
    (hp : ∀ x : (normalizedInductionFunctor (family.decomposition a.roots)
        (family.closedUnipotent a.roots)).obj
          (bernsteinLiteralLeviRep i ν a.roots
            (rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation)),
      SmoothRep.hom (z.app ((normalizedInductionFunctor (family.decomposition a.roots)
        (family.closedUnipotent a.roots)).obj
          (bernsteinLiteralLeviRep i ν a.roots
            (rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation)))) x =
        p • x)
    (hq : ∀ y : (normalizedInductionFunctor (family.decomposition b.roots)
        (family.closedUnipotent b.roots)).obj
          (bernsteinLiteralLeviRep i ν b.roots
            (rationalUnramifiedTwist (bernsteinLeviScheme i ν b.roots) ω' b.representation)),
      SmoothRep.hom (z.app ((normalizedInductionFunctor (family.decomposition b.roots)
        (family.closedUnipotent b.roots)).obj
          (bernsteinLiteralLeviRep i ν b.roots
            (rationalUnramifiedTwist (bernsteinLeviScheme i ν b.roots) ω' b.representation)))) y =
        q • y) :
    p = q := by
  obtain ⟨π, hπ, h1, h2⟩ := exists_common_irreducible_subquotient i ν family hI a b ω ω' h
  have hne := Langlands.Classification.SegmentHeadSupport.nontrivial_of_isIrreducible hπ
  exact SmoothRep.scalar_unique (z.app π) (SmoothRep.centerScalar_of_isSubquotient z h1 hp)
    (SmoothRep.centerScalar_of_isSubquotient z h2 hq)

/-- Under the first sentence of VI.10.4 (with Remark 1), an element of the centre acts on
the inductions `i_P^G(ρ ⊗ ω)` of a datum by the values of a polynomial function on `X(M)`. -/
theorem exists_twistInduction_scalars (hS1 : BernsteinBlockCenterFunctionsStatement.{uF, uV})
    (z : CatCenter (SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)))
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family) :
    ∃ g : unramifiedCharacters
        (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul) → ℂ,
      g ∈ unramifiedRegularFunctions
        (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul) ∧
      ∀ (ω : unramifiedCharacters
          (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul))
        (x : (normalizedInductionFunctor (family.decomposition a.roots)
          (family.closedUnipotent a.roots)).obj
            (bernsteinLiteralLeviRep i ν a.roots
              (rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation))),
        SmoothRep.hom (z.app ((normalizedInductionFunctor (family.decomposition a.roots)
          (family.closedUnipotent a.roots)).obj
            (bernsteinLiteralLeviRep i ν a.roots
              (rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation))))
          x = g ω • x := by
  obtain ⟨hmem, O, hO, e, he⟩ := hS1 F G T i ν family a
  let zr := catCenterRestrict
    (bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family a)) z
  refine ⟨(e zr).1, ?_, ?_⟩
  · have h1 := (e zr).2
    rw [← SetLike.mem_coe, hO] at h1
    exact h1.1
  · intro ω x
    have h2 := he zr ω (hmem ω) x
    exact h2

/-- Under the first sentence of VI.10.4 (with Remark 1), two elements of the centre that agree
on every `i_P^G(ρ ⊗ ω)` of a datum agree on the whole saturated block of the datum. -/
theorem center_app_eq_of_twistInduction (hS1 : BernsteinBlockCenterFunctionsStatement.{uF, uV})
    (z z' : CatCenter (SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)))
    (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (h : ∀ ω : unramifiedCharacters
        (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul),
      z.app ((normalizedInductionFunctor (family.decomposition a.roots)
          (family.closedUnipotent a.roots)).obj
            (bernsteinLiteralLeviRep i ν a.roots
              (rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation))) =
        z'.app ((normalizedInductionFunctor (family.decomposition a.roots)
          (family.closedUnipotent a.roots)).obj
            (bernsteinLiteralLeviRep i ν a.roots
              (rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation))))
    (X : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))
    (hX : bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family a) X) :
    z.app X = z'.app X := by
  obtain ⟨hmem, O, hO, e, he⟩ := hS1 F G T i ν family a
  have hzz : catCenterRestrict
      (bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family a)) z =
      catCenterRestrict
        (bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family a)) z' := by
    apply e.injective
    apply Subtype.ext
    funext ω
    have hne' := nontrivial_twistInduction i ν family a
    have hne := hne' ω
    have h1 := he (catCenterRestrict
      (bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family a)) z) ω
      (hmem ω)
    have h2 := he (catCenterRestrict
      (bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family a)) z') ω
      (hmem ω)
    have hω := h ω
    simp only [catCenterRestrict_app_hom] at h1 h2
    rw [← hω] at h2
    exact SmoothRep.scalar_unique _ h1 h2
  exact catCenterRestrict_app_eq hzz hX

/-- Under the first sentence of VI.10.4 (with Remark 1), a polynomial function `g` on `X(M_{a₀})`
constant on association classes is the family of scalars of an element of the centre of the
block of `a₀` on the inductions `i_P^G(ρ_{a₀} ⊗ ω)`. -/
theorem exists_blockCenter_of_function (hS1 : BernsteinBlockCenterFunctionsStatement.{uF, uV})
    (s : BernsteinInertialClass.{uF, max uF uV} i ν family)
    (a₀ : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (h₀ : bernsteinInertialClass i ν family a₀ = s)
    (g : unramifiedCharacters
        (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a₀.roots) χ).toMul) → ℂ)
    (hreg : g ∈ unramifiedRegularFunctions
        (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a₀.roots) χ).toMul))
    (hinv : ∀ ω ω' : unramifiedCharacters
        (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a₀.roots) χ).toMul),
      (∃ c : RationalLeviConjugacy (Standard.leviHom i ν (rootSet i ν a₀.roots))
          (Standard.leviHom i ν (rootSet i ν a₀.roots)),
        Nonempty (rationalUnramifiedTwist (bernsteinLeviScheme i ν a₀.roots) ω a₀.representation ≅
          rationalIsoPullback c.iso
            (rationalUnramifiedTwist (bernsteinLeviScheme i ν a₀.roots) ω' a₀.representation))) →
        g ω = g ω') :
    ∃ zs : CatCenter (BernsteinSaturatedBlock i ν family s),
      ∀ (ω : unramifiedCharacters
          (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a₀.roots) χ).toMul))
        (hω : bernsteinSaturatedBlockProperty i ν family s
          ((normalizedInductionFunctor (family.decomposition a₀.roots)
            (family.closedUnipotent a₀.roots)).obj
              (bernsteinLiteralLeviRep i ν a₀.roots
                (rationalUnramifiedTwist (bernsteinLeviScheme i ν a₀.roots) ω a₀.representation))))
        (x : (normalizedInductionFunctor (family.decomposition a₀.roots)
            (family.closedUnipotent a₀.roots)).obj
              (bernsteinLiteralLeviRep i ν a₀.roots
                (rationalUnramifiedTwist (bernsteinLeviScheme i ν a₀.roots) ω a₀.representation))),
        SmoothRep.hom (zs.app ⟨_, hω⟩).hom x = g ω • x := by
  subst h₀
  obtain ⟨hmem, O, hO, e, he⟩ := hS1 F G T i ν family a₀
  have hgO : g ∈ O := by
    rw [← SetLike.mem_coe, hO]
    exact ⟨hreg, hinv⟩
  refine ⟨e.symm ⟨g, hgO⟩, ?_⟩
  intro ω hω x
  have h1 := he (e.symm ⟨g, hgO⟩) ω hω x
  rw [RingEquiv.apply_symm_apply] at h1
  exact h1

/-- Under the first sentence of VI.10.4 (with Remark 1) and VI.5.4: if an element `zs` of the
centre of the block `s` acts on the inductions of a datum `a₀` of `s` by the values of an
association-compatible family `f`, it acts by the values of `f` on the inductions of every
datum `a` of `s`. -/
theorem blockCenter_scalar_of_related (hS1 : BernsteinBlockCenterFunctionsStatement.{uF, uV})
    (hI : BernsteinAssociatedSupportInvarianceStatement.{uF, uV} i ν family)
    (s : BernsteinInertialClass.{uF, max uF uV} i ν family)
    (zs : CatCenter (BernsteinSaturatedBlock i ν family s))
    (f : (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family) →
      (rationalPoints (bernsteinLeviScheme i ν a.roots) →* ℂˣ) → ℂ)
    (hcompat : ∀ (a b : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
      (ω : unramifiedCharacters
        (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul))
      (ω' : unramifiedCharacters
        (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν b.roots) χ).toMul)),
      (∃ c : RationalLeviConjugacy (Standard.leviHom i ν (rootSet i ν a.roots))
          (Standard.leviHom i ν (rootSet i ν b.roots)),
        Nonempty (rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation ≅
          rationalIsoPullback c.iso
            (rationalUnramifiedTwist (bernsteinLeviScheme i ν b.roots) ω' b.representation))) →
        f a ω.val.toMonoidHom = f b ω'.val.toMonoidHom)
    (a₀ a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
    (h₀ : bernsteinInertialClass i ν family a₀ = s) (ha : bernsteinInertialClass i ν family a = s)
    (hzs : ∀ (ω : unramifiedCharacters
          (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a₀.roots) χ).toMul))
        (hω : bernsteinSaturatedBlockProperty i ν family s
          ((normalizedInductionFunctor (family.decomposition a₀.roots)
            (family.closedUnipotent a₀.roots)).obj
              (bernsteinLiteralLeviRep i ν a₀.roots
                (rationalUnramifiedTwist (bernsteinLeviScheme i ν a₀.roots) ω a₀.representation))))
        (x : (normalizedInductionFunctor (family.decomposition a₀.roots)
            (family.closedUnipotent a₀.roots)).obj
              (bernsteinLiteralLeviRep i ν a₀.roots
                (rationalUnramifiedTwist (bernsteinLeviScheme i ν a₀.roots) ω a₀.representation))),
        SmoothRep.hom (zs.app ⟨_, hω⟩).hom x = f a₀ ω.val.toMonoidHom • x)
    (ω : unramifiedCharacters
      (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul))
    (hω : bernsteinSaturatedBlockProperty i ν family s
      ((normalizedInductionFunctor (family.decomposition a.roots)
        (family.closedUnipotent a.roots)).obj
          (bernsteinLiteralLeviRep i ν a.roots
            (rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation))))
    (x : (normalizedInductionFunctor (family.decomposition a.roots)
        (family.closedUnipotent a.roots)).obj
          (bernsteinLiteralLeviRep i ν a.roots
            (rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation))) :
    SmoothRep.hom (zs.app ⟨_, hω⟩).hom x = f a ω.val.toMonoidHom • x := by
  subst ha
  obtain ⟨hmem, O, hO, e, he⟩ := hS1 F G T i ν family a
  have hrel : IsBernsteinInertiaRelated i ν family a₀ a :=
    (bernsteinInertialClass_eq_iff i ν family a₀ a).mp h₀
  have htr := exists_twist_association i ν family a₀ a hrel
  obtain ⟨ω₀, hassoc⟩ := htr ω
  have hfeq := hcompat a₀ a ω₀ ω hassoc
  have hcom := exists_common_irreducible_subquotient i ν family hI a₀ a
  obtain ⟨π, hπ, h1, h2⟩ := hcom ω₀ ω hassoc
  have hmem₀' := twistInduction_mem_saturatedBlock i ν family a₀
  have hmem₀ := hmem₀' ω₀
  rw [h₀] at hmem₀
  have hclosed : ∀ {V W : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)},
      bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family a) V →
        SmoothRep.IsSubquotient W V →
          bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family a) W :=
    fun hV hWV => bernsteinSaturatedBlockProperty_of_isSubquotient i ν family hV hWV
  have hπmem := hclosed hω h2
  have hne := Langlands.Classification.SegmentHeadSupport.nontrivial_of_isIrreducible hπ
  have k₀ := hzs ω₀ hmem₀
  have k₁ := SmoothRep.fullSubcategory_centerScalar_of_isSubquotient hclosed zs hmem₀ hπmem h1 k₀
  have kω := he zs ω hω
  have k₂ := SmoothRep.fullSubcategory_centerScalar_of_isSubquotient hclosed zs hω hπmem h2 kω
  have hc := SmoothRep.scalar_unique _ k₁ k₂
  rw [kω x, ← hc, hfeq]

/-- Under the first sentence of VI.10.4 (with Remark 1) and VI.5.4, an association-compatible
family `f` of polynomial functions gives, for every inertial class `s`, an element of the
centre of the block of `s` acting on the inductions of every datum of `s` by the values of
`f`. -/
theorem exists_blockCenter (hS1 : BernsteinBlockCenterFunctionsStatement.{uF, uV})
    (hI : BernsteinAssociatedSupportInvarianceStatement.{uF, uV} i ν family)
    (f : (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family) →
      (rationalPoints (bernsteinLeviScheme i ν a.roots) →* ℂˣ) → ℂ)
    (hreg : ∀ a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family,
      (fun ω : unramifiedCharacters
          (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul) =>
        f a ω.val.toMonoidHom) ∈ unramifiedRegularFunctions
        (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul))
    (hcompat : ∀ (a b : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
      (ω : unramifiedCharacters
        (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul))
      (ω' : unramifiedCharacters
        (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν b.roots) χ).toMul)),
      (∃ c : RationalLeviConjugacy (Standard.leviHom i ν (rootSet i ν a.roots))
          (Standard.leviHom i ν (rootSet i ν b.roots)),
        Nonempty (rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation ≅
          rationalIsoPullback c.iso
            (rationalUnramifiedTwist (bernsteinLeviScheme i ν b.roots) ω' b.representation))) →
        f a ω.val.toMonoidHom = f b ω'.val.toMonoidHom)
    (s : BernsteinInertialClass.{uF, max uF uV} i ν family) :
    ∃ zs : CatCenter (BernsteinSaturatedBlock i ν family s),
      ∀ (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family),
        bernsteinInertialClass i ν family a = s →
        ∀ (ω : unramifiedCharacters
            (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul))
          (hω : bernsteinSaturatedBlockProperty i ν family s
            ((normalizedInductionFunctor (family.decomposition a.roots)
              (family.closedUnipotent a.roots)).obj
                (bernsteinLiteralLeviRep i ν a.roots
                  (rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation))))
          (x : (normalizedInductionFunctor (family.decomposition a.roots)
              (family.closedUnipotent a.roots)).obj
                (bernsteinLiteralLeviRep i ν a.roots
                  (rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation))),
          SmoothRep.hom (zs.app ⟨_, hω⟩).hom x = f a ω.val.toMonoidHom • x := by
  obtain ⟨a₀, h₀⟩ := exists_bernsteinInertialClass_eq i ν family s
  obtain ⟨zs, hzs⟩ := exists_blockCenter_of_function i ν family hS1 s a₀ h₀
    (fun ω => f a₀ ω.val.toMonoidHom) (hreg a₀) (fun ω ω' hωω' => hcompat a₀ a₀ ω ω' hωω')
  exact ⟨zs, fun a ha => blockCenter_scalar_of_related i ν family hS1 hI s zs f hcompat a₀ a h₀ ha
    hzs⟩

/-- Extension by zero of a function on `X(M)` to all characters of `M(F)`. -/
def extendUnramified (a : BernsteinCuspidalDatum.{uF, uV} i ν family)
    (g : unramifiedCharacters
      (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul) → ℂ) :
    (rationalPoints (bernsteinLeviScheme i ν a.roots) →* ℂˣ) → ℂ :=
  Function.extend (fun ω : unramifiedCharacters
    (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul) =>
      ω.val.toMonoidHom) g 0

omit [LocallyOfFiniteType G.X.hom] in
theorem extendUnramified_apply (a : BernsteinCuspidalDatum.{uF, uV} i ν family)
    (g : unramifiedCharacters
      (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul) → ℂ)
    (ω : unramifiedCharacters
      (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul)) :
    extendUnramified i ν family a g ω.val.toMonoidHom = g ω := by
  have hinj : Function.Injective (fun ω : unramifiedCharacters
      (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul) =>
        ω.val.toMonoidHom) := by
    intro ω₁ ω₂ h
    apply Subtype.ext
    ext x
    exact congrArg (fun φ => ((φ x : ℂˣ) : ℂ)) h
  exact hinj.extend_apply g 0 ω

end Helpers

attribute [local instance] instCenterFunctionsReductionLeviTopology

/-- Derived reduction: Renard VI.10.4, Theorem, second sentence, with Remark 1
(`BernsteinCenterFunctionsStatement`), follows from the first sentence with Remark 1
(`BernsteinBlockCenterFunctionsStatement`), the Bernstein decomposition of VI.7.2 at carriers
in `Type (max uF uV)` and the invariance of irreducible induction-subquotients under
association (VI.5.4, `BernsteinAssociatedSupportInvarianceStatement`) for every standard
family. -/
def BernsteinCenterFunctionsReductionStatement : Prop :=
  BernsteinBlockCenterFunctionsStatement.{uF, uV} →
    BernsteinDecompositionStatement.{uF, max uF uV} →
    (∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
        [IsNonarchimedeanLocalField F]
        (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
        [LocallyOfFiniteType G.X.hom]
        (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
        (ν : cocharacterLattice T),
        letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
        letI : TopologicalSpace (rationalPoints G) := pointTopology
        ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
          (family : BernsteinStandardFamily i ν),
          BernsteinAssociatedSupportInvarianceStatement.{uF, uV} i ν family) →
    BernsteinCenterFunctionsStatement.{uF, uV}

/-- Proof of the reduction. For `z` in the centre, the first sentence applied to the
restriction of `z` to the block of each datum `a` gives a polynomial function on `X(M_a)` of
scalars; associated twists share an irreducible subquotient (VI.5.4), forcing the
compatibility. Injectivity: by the first sentence, `z` restricted to each block is determined
by its scalars, and the decomposition (VI.7.2) makes `z` determined by its restrictions.
Surjectivity: on each class `s`, the first sentence applied to a representative `a₀` gives a
block-central element with the prescribed scalars on the inductions of `a₀`, hence (twist
transport and VI.5.4) on the inductions of every datum of `s`; these are assembled over the
decomposition into an element of the centre. -/
theorem bernsteinCenterFunctions_reduction :
    BernsteinCenterFunctionsReductionStatement.{uF, uV} := by
  intro hS1 hdec hinv F _ _ _ _ G _ _ T i ν
  let : TopologicalSpace (rationalPoints G) := pointTopology
  intro _ _ family
  have hD := hdec F G T i ν family
  have hI := hinv F G T i ν family
  refine ⟨?_, ?_, ?_⟩
  · intro z
    have hg := exists_twistInduction_scalars i ν family hS1 z
    choose g hgreg hgsc using hg
    refine ⟨fun a => extendUnramified i ν family a (g a), ?_, ?_⟩
    · intro a Xa twista inda
      refine ⟨?_, ?_⟩
      · have hfun : (fun ω : Xa => extendUnramified i ν family a (g a) ω.val.toMonoidHom) =
            g a := funext fun ω => extendUnramified_apply i ν family a (g a) ω
        show (fun ω : Xa => extendUnramified i ν family a (g a) ω.val.toMonoidHom) ∈ _
        rw [hfun]
        exact hgreg a
      · intro b Xb twistb indb ω ω' hωω'
        show extendUnramified i ν family a (g a) ω.val.toMonoidHom =
          extendUnramified i ν family b (g b) ω'.val.toMonoidHom
        rw [extendUnramified_apply, extendUnramified_apply]
        have hsa := hgsc a ω
        have hsb := hgsc b ω'
        have key := scalar_eq_of_twistAssociated i ν family hI z a b ω ω' hωω'
          (p := g a ω) (q := g b ω')
        exact key hsa hsb
    · intro a Xa twista inda ω x
      show _ = extendUnramified i ν family a (g a) ω.val.toMonoidHom • x
      rw [extendUnramified_apply]
      have hsa := hgsc a ω
      exact hsa x
  · intro z z' hzz'
    apply catCenter_ext_of_everyObjectIsCoproduct hD.1
    intro s X hX
    obtain ⟨a, rfl⟩ := exists_bernsteinInertialClass_eq i ν family s
    have ha := hzz' a
    have hXs := (bernsteinBlockProperty_iff_saturated _ X).mp hX
    exact center_app_eq_of_twistInduction i ν family hS1 z z' a ha X hXs
  · intro f hf
    have hzsex := exists_blockCenter i ν family hS1 hI f (fun a => (hf a).1)
      (fun a b => (hf a).2 b)
    choose zs hzs using hzsex
    let w : ∀ (s : BernsteinInertialClass.{uF, max uF uV} i ν family)
        (X : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)),
        bernsteinBlockProperty.{uF, max uF uV} i ν family s X → (X ⟶ X) :=
      fun s X hX => ((zs s).app ⟨X, (bernsteinBlockProperty_iff_saturated s X).mp hX⟩).hom
    have hw : ∀ (s : BernsteinInertialClass.{uF, max uF uV} i ν family)
        (X Y : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))
        (hX : bernsteinBlockProperty.{uF, max uF uV} i ν family s X)
        (hY : bernsteinBlockProperty.{uF, max uF uV} i ν family s Y) (g : X ⟶ Y),
        g ≫ w s Y hY = w s X hX ≫ g := by
      intro s X Y hX hY g
      have h := CatCenter.naturality (zs s)
        (ObjectProperty.homMk g :
          (⟨X, (bernsteinBlockProperty_iff_saturated s X).mp hX⟩ :
            BernsteinSaturatedBlock i ν family s) ⟶
          ⟨Y, (bernsteinBlockProperty_iff_saturated s Y).mp hY⟩)
      have h' := congrArg (fun φ => φ.hom) h
      simp only [ObjectProperty.FullSubcategory.comp_hom] at h'
      exact h'
    refine ⟨SmoothRep.assembledCenter hD w hw, ?_⟩
    intro a Xa twista inda ω x
    have hmem := twistInduction_mem_saturatedBlock i ν family a
    have hmemω := hmem ω
    have hblock := (bernsteinBlockProperty_iff_saturated _ _).mpr hmemω
    have happ := SmoothRep.assembledCenter_app_of_mem hD w hw
      (bernsteinInertialClass i ν family a) _ hblock
    rw [happ]
    have k := hzs (bernsteinInertialClass i ν family a) a rfl ω
    exact k _ x

end Langlands.CuspidalSupport
