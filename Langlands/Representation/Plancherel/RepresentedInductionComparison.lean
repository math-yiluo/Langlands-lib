import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.Representation.Plancherel.ParabolicPointIntertwiningRegion
import Langlands.Representation.Plancherel.CompactIntertwiningFamilies
import Langlands.Representation.Plancherel.ParabolicRadicalUnimodularity
import Langlands.Representation.Classification.SupercuspidalSupport

noncomputable section

set_option backward.isDefEq.respectTransparency.types true

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

open Aubert.General Aubert.General.RepresentedParabolic

private def normalizedInductionSubgroupLeviEquiv
    {H : Type*} [Group H] [TopologicalSpace H]
    [LocallyCompactSpace H] [NonarchimedeanGroup H]
    {P M U P' M' U' : Subgroup H}
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set H))
    (h' : IsSemidirectDecomposition P' M' U') (hU' : IsClosed (U' : Set H))
    (eP : P = P') (eM : M = M') (eU : U = U')
    (hδ : IsUnimodularModulus U' hU')
    {σ : SmoothRep ℂ M} {τ : SmoothRep ℂ M'}
    (e : (SmoothRep.pullback (subgroupCongrContinuous eM).symm σ).representation.Equiv
      τ.representation) :
    ((normalizedInductionFunctor h hU).obj σ).representation.Equiv
      ((DynamicNormalization.leviTwistedInductionFunctor h' hU').obj τ).representation := by
  subst eP eM eU
  let e₀ : σ.representation.Equiv
      (SmoothRep.pullback (subgroupCongrContinuous (rfl : M = M)).symm σ).representation :=
    Representation.Equiv.mk (LinearEquiv.refl ℂ σ) (fun _ => rfl)
  exact (normalizedInductionEquivOfEquiv h hU (e₀.trans e)).trans
    (normalizedInductionLeviEquiv h' hU' hδ τ)

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G M P U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine M.X.left]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

local instance representedInductionComparisonAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance representedInductionComparisonAmbientPointTopology :
    TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
local instance representedInductionComparisonLeviPointTopology :
    TopologicalSpace (rationalPoints M) := rationalPointTopology F M.X
local instance representedInductionComparisonFieldT2Space : T2Space F :=
  Langlands.BruhatTits.localField_t2Space F

/-- Pull a representation of the literal Levi subgroup back to its intrinsic
rational points, keeping the original vector space. -/
abbrev intrinsicLeviRep (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)) :
    SmoothRep.{0, u, uV} ℂ (rationalPoints M) :=
  SmoothRep.pullback (parabolicLeviPointHomeomorph r) π

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
/-- The two published Levi point maps are the same actual point map. -/
theorem parabolicLeviPointHomeomorph_eq_leviPointsEquiv :
    parabolicLeviPointHomeomorph r =
      leviPointsEquiv p l r.isCompatible.parabolic r.isCompatible.levi := by
  ext m
  rfl

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
/-- Intrinsic Levi pullback preserves irreducibility. -/
theorem intrinsicLeviRep_isIrreducible_iff
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)) :
    (intrinsicLeviRep r π).IsIrreducible ↔ π.IsIrreducible :=
  isIrreducible_comp_continuousMulEquiv_iff π.representation
    (parabolicLeviPointHomeomorph r)

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

set_option maxHeartbeats 800000 in
/-- Pulling the corresponding intrinsic twist through the explicit subgroup
identification recovers the original twist on the same vector space. -/
def representedLeviTwistEquiv
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l))
    (χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r)) :
    letI := leviPoints_nonarchimedeanGroup p l r.isCompatible.parabolic r.isCompatible.levi
    (SmoothRep.pullback
      (subgroupCongrContinuous (pointImage_eq_range_carrier (l ≫ p))).symm
      (SmoothRep.pullback
        (leviPointsEquiv p l r.isCompatible.parabolic r.isCompatible.levi).symm
        ((intrinsicLeviRep r π).twist
          (((parabolicLeviUnramifiedCharactersHomeomorph r).symm χ).val.toMonoidHom)
          (unramifiedCharacter_isOpen_ker _ _)))).representation.Equiv
      (π.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker _ χ)).representation := by
  letI := leviPoints_nonarchimedeanGroup p l r.isCompatible.parabolic r.isCompatible.levi
  let c := subgroupCongrContinuous (pointImage_eq_range_carrier (l ≫ p))
  let e := leviPointsEquiv p l r.isCompatible.parabolic r.isCompatible.levi
  refine Representation.Equiv.mk (LinearEquiv.refl ℂ π) ?_
  intro m
  apply LinearMap.ext
  intro v
  have hm : parabolicLeviPointHomeomorph r (e.symm (c.symm m)) = m := by
    apply Subtype.ext
    change rationalPoints.map (l ≫ p) (e.symm (c.symm m)) = (m : rationalPoints G)
    exact congrArg Subtype.val (e.apply_symm_apply (c.symm m))
  change (((parabolicLeviUnramifiedCharactersHomeomorph r).symm χ).val
      (e.symm (c.symm m)) : ℂ) •
      π.representation (parabolicLeviPointHomeomorph r (e.symm (c.symm m))) v =
    (χ.val m : ℂ) • π.representation m v
  rw [parabolicLeviUnramifiedCharactersHomeomorph_symm_apply, hm]

set_option maxHeartbeats 800000 in
/-- The represented induction of the corresponding intrinsic twist is
equivalent to the actual positive Levi-normalized induction, for every
supplied geometric radical and semidirect decomposition. -/
def representedInductionLeviEquiv
    (hG : IsConnectedReductive G)
    {U' : GroupScheme (Spec (CommRingCat.of F))} {n' : U' ⟶ P}
    (hn' : LeviSubgroup.IsGeometricUnipotentRadical n')
    (hmul : IsIso (subgroupMultiplication l n'))
    {n : U ⟶ P} (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
    (h : IsSemidirectDecomposition
      ((SubgroupFunctor.range p).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))))
      (parabolicLeviPointSubgroup p l)
      ((SubgroupFunctor.range (n ≫ p)).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F))))))
    (hU : IsClosed (((SubgroupFunctor.range (n ≫ p)).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of F))))) : Set (rationalPoints G)))
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l))
    (χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r)) :
    letI := leviPoints_nonarchimedeanGroup p l r.isCompatible.parabolic r.isCompatible.levi
    ((leviInductionFunctor p l n' r.isCompatible.parabolic
        hn' r.isCompatible.levi hmul).obj
      ((intrinsicLeviRep r π).twist
        (((parabolicLeviUnramifiedCharactersHomeomorph r).symm χ).val.toMonoidHom)
        (unramifiedCharacter_isOpen_ker _ _))).representation.Equiv
      (UnramifiedLeviInduction h hU
        (parabolicLeviRationalNormCharacters r) χ π).representation := by
  letI := hG.smooth
  letI := leviPoints_nonarchimedeanGroup p l r.isCompatible.parabolic r.isCompatible.levi
  rw [leviInductionFunctor_obj]
  let h₀ := isSemidirectDecomposition_pointImage p l n'
    r.isCompatible.parabolic.isClosedSubgroup hn' hmul
  let hU₀ : @IsClosed (rationalPoints G) (rationalPointTopology F G.X)
      (pointImage (n' ≫ p) : Set (rationalPoints G)) :=
    isClosed_pointImage_comp p n'
      r.isCompatible.parabolic.isClosedSubgroup hn'.1.isClosedSubgroup
  have he : pointImage (n' ≫ p) =
      (SubgroupFunctor.range (n ≫ p)).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of F)))) := by
    change (SubgroupFunctor.range (n' ≫ p)).carrier _ = _
    rw [r.range_comp_radical_eq hn', r.range_comp_radical_eq hn]
    rfl
  let E := normalizedInductionSubgroupLeviEquiv h₀ hU₀ h hU
    (pointImage_eq_range_carrier p) (pointImage_eq_range_carrier (l ≫ p)) he
    (parabolicRadical_isUnimodular F G hG A M P U p l a n r hn hU)
    (representedLeviTwistEquiv r π χ)
  dsimp only [inductionFunctor, UnramifiedLeviInduction]
  exact E

variable (hG : IsConnectedReductive G)
  {n : U ⟶ P} (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
  (h : IsSemidirectDecomposition
    ((SubgroupFunctor.range p).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F)))))
    (parabolicLeviPointSubgroup p l)
    ((SubgroupFunctor.range (n ≫ p)).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F))))))
  (hU : IsClosed (((SubgroupFunctor.range (n ≫ p)).carrier
    (Over.mk (𝟙 (Spec (CommRingCat.of F))))) : Set (rationalPoints G)))

set_option maxHeartbeats 800000 in
/-- The canonical actual radical of the root presentation supplies the represented
model, without asking for an additional radical or multiplication isomorphism. -/
def canonicalRepresentedInductionLeviEquiv
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l))
    (χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r)) :
    letI := hG.smooth
    letI := leviPoints_nonarchimedeanGroup p l r.isCompatible.parabolic r.isCompatible.levi
    ((leviInductionFunctor p l r.radicalHom r.isCompatible.parabolic
        r.leviSubgroup_isGeometricUnipotentRadical_radicalHom
        r.isCompatible.levi r.isIso_subgroupMultiplication_radicalHom).obj
      ((intrinsicLeviRep r π).twist
        (((parabolicLeviUnramifiedCharactersHomeomorph r).symm χ).val.toMonoidHom)
        (unramifiedCharacter_isOpen_ker _ _))).representation.Equiv
      (UnramifiedLeviInduction h hU
        (parabolicLeviRationalNormCharacters r) χ π).representation := by
  letI := hG.smooth
  exact representedInductionLeviEquiv r hG
    r.leviSubgroup_isGeometricUnipotentRadical_radicalHom
    r.isIso_subgroupMultiplication_radicalHom hn h hU π χ

include hG hn in
set_option maxHeartbeats 800000 in
/-- A common detector for represented intrinsic-Levi twists detects all literal
positive Levi-normalized twists on the full rational-norm parameter space. -/
theorem representedInduction_uniformDetector_transfer
    {U' : GroupScheme (Spec (CommRingCat.of F))} {n' : U' ⟶ P}
    (hn' : LeviSubgroup.IsGeometricUnipotentRadical n')
    (hmul : IsIso (subgroupMultiplication l n'))
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l))
    (K : OpenSubgroup (rationalPoints G))
    (hdet :
      letI := leviPoints_nonarchimedeanGroup p l r.isCompatible.parabolic r.isCompatible.levi
      ∀ (ψ : unramifiedCharacters
          (fun κ : rationalCharacters M => (rationalNormCharacters M κ).toMul))
        (D : SmoothRep.{0, u, max u uV} ℂ (rationalPoints G)),
        D.IsIrreducible →
        SmoothRep.IsSubquotient D
          ((leviInductionFunctor p l n' r.isCompatible.parabolic hn'
              r.isCompatible.levi hmul).obj
            ((intrinsicLeviRep r π).twist ψ.val.toMonoidHom
              (unramifiedCharacter_isOpen_ker _ ψ))) →
        ∃ v : D, v ∈ fixedVectors D.representation K.toSubgroup ∧ v ≠ 0) :
    ∀ (χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r))
      (D : SmoothRep.{0, u, max u uV} ℂ (rationalPoints G)),
      D.IsIrreducible →
      SmoothRep.IsSubquotient D
        (UnramifiedLeviInduction h hU (parabolicLeviRationalNormCharacters r) χ π) →
      ∃ v : D, v ∈ fixedVectors D.representation K.toSubgroup ∧ v ≠ 0 := by
  let := leviPoints_nonarchimedeanGroup p l r.isCompatible.parabolic r.isCompatible.levi
  intro χ D hD hsub
  apply hdet ((parabolicLeviUnramifiedCharactersHomeomorph r).symm χ) D hD
  exact hsub.of_iso_right (SmoothRep.mkIso
    (representedInductionLeviEquiv r hG hn' hmul hn h hU π χ).symm)

end Langlands.Plancherel
