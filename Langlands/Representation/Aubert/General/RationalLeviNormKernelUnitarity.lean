import Langlands.Representation.Aubert.General.RationalCompactRestrictionUnitarity
import Langlands.Representation.Aubert.General.RationalLeviFullCenterUnitary
import Langlands.Representation.Aubert.General.RationalLeviNormTopology
import Langlands.Representation.MatrixCoefficient.GroupTransport
import Langlands.Topology.Nonarchimedean.Subgroup

/-! # Positive forms on the literal Levi from its canonical norm kernel -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) (I : Finset (SimpleRoot i ν))

local instance leviNormKernelAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance leviNormKernelClosedImmersion :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance leviNormKernelAffine :
    IsAffine (Standard.leviScheme i ν (rootSet i ν I)).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance leviNormKernelAmbientTopology : TopologicalSpace (rationalPoints G) :=
  pointTopology
local instance leviNormKernelPointTopology :
    TopologicalSpace (rationalPoints (Standard.leviScheme i ν (rootSet i ν I))) :=
  rationalPointTopology k (Standard.leviScheme i ν (rootSet i ν I)).X

variable [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] [T2Space (rationalPoints G)]
  (hMI : IsClosed (levi i ν I : Set (rationalPoints G)))

local instance leviNormKernelPointT2 :
    T2Space (rationalPoints (Standard.leviScheme i ν (rootSet i ν I))) :=
  (leviRationalPointHomeomorph i ν I).toHomeomorph.isEmbedding.t2Space
local instance leviNormKernelPointTopologicalGroup :
    IsTopologicalGroup (rationalPoints (Standard.leviScheme i ν (rootSet i ν I))) :=
  (leviRationalPointHomeomorph i ν I).toHomeomorph.isInducing.isTopologicalGroup
    (leviRationalPointHomeomorph i ν I).toMulEquiv
local instance leviNormKernelPointNonarchimedean :
    NonarchimedeanGroup (rationalPoints (Standard.leviScheme i ν (rootSet i ν I))) :=
  NonarchimedeanGroup.nonarchimedean_of_emb
    (leviRationalPointHomeomorph i ν I).symm.toMonoidHom
    (leviRationalPointHomeomorph i ν I).symm.toHomeomorph.isOpenEmbedding

variable {A : CommGroupScheme (Spec (CommRingCat.of k))}
  (s : A.toGrp ⟶ Standard.leviScheme i ν (rootSet i ν I)) (hs : IsCentral s)
  (hindex : (Plancherel.RenardCartan.splitValuationImage s).FiniteIndex)
  (σ : SmoothRep.{0, u, v} ℂ (levi i ν I)) (hirr : σ.IsIrreducible)
  (hcoeff : HasCompactSmoothDualCoefficients
    (SmoothRep.restrictSubgroup
      (Plancherel.rationalCommonNormKernel (Standard.leviScheme i ν (rootSet i ν I)))
      ((SmoothRep.pullbackFunctor (leviRationalPointHomeomorph i ν I)).obj σ)).representation)

include hMI s hs hindex hirr hcoeff

/-- Pull the full unitary central character to the actual Levi point group,
construct its coefficient integral there, and keep the same positive form
on the original literal-Levi representation. -/
def leviNormKernelPositiveForm (c : UnitaryCentralCharacter σ.representation) :
    InvariantPositiveForm σ.representation := by
  haveI : LocallyCompactSpace (levi i ν I) := hMI.locallyCompactSpace
  haveI : LocallyCompactSpace
      (rationalPoints (Standard.leviScheme i ν (rootSet i ν I))) :=
    (leviRationalPointHomeomorph i ν I).toHomeomorph.isClosedEmbedding.locallyCompactSpace
  let e := leviRationalPointHomeomorph i ν I
  let σL := (SmoothRep.pullbackFunctor e).obj σ
  have hσL : σL.IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff σ.representation e).mpr hirr
  let b : InvariantPositiveForm σL.representation :=
    rationalNormKernelPositiveForm s hs hindex σL hσL
      (c.compContinuousMulEquiv e) hcoeff
  exact
    { toInnerProductCore := b.toInnerProductCore
      invariant m v w := by
        change b.inner (σ.representation m v) (σ.representation m w) = b.inner v w
        have h := b.invariant (e.symm m) v w
        change b.inner (σ.representation (e (e.symm m)) v)
          (σ.representation (e (e.symm m)) w) = b.inner v w at h
        simpa only [e.apply_symm_apply] using h }

/-- The literal inducing representation is unitarizable without an
admissibility premise once its canonical norm-kernel coefficients are compact. -/
theorem isUnitarizable_levi_of_compact_normKernel_restriction
    (c : UnitaryCentralCharacter σ.representation) :
    IsUnitarizable σ.representation :=
  ⟨leviNormKernelPositiveForm i ν I hMI s hs hindex σ hirr hcoeff c⟩

/-- The actual full-center extension from the Levi-central torus supplies
the central-character input of the literal positive-form construction. -/
def leviNormKernelPositiveForm_of_centralTorus
    (hSplit : StandardLeviSplitComponentStatement.{u})
    (hCompact : CenterSplitComponentCompactnessStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    (χ : Subgroup.center (levi i ν I) →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (Subgroup.center (levi i ν I))))
    (htorus : ∀ t : leviCentralTorusPoints i ν I,
      ‖(χ (leviCentralTorusPointToCenter i ν I t) : ℂ)‖ = 1)
    (hacts : ∀ (z : Subgroup.center (levi i ν I)) (v : σ),
      σ.representation z v = (χ z : ℂ) • v) :
    InvariantPositiveForm σ.representation :=
  leviNormKernelPositiveForm i ν I hMI s hs hindex σ hirr hcoeff
    (leviUnitaryCentralCharacter_of_centralTorus i ν hSplit hCompact hG hi hν I
      σ.representation χ hχ htorus hacts)

end Langlands.Aubert.General.RationalPointFamily
