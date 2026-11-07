import Langlands.Representation.Geometric.CoefficientClosedSubgroupMackey
import Langlands.Representation.Geometric.CompactSmoothComparison
import Langlands.Representation.Jacquet.CoefficientRestrictedFiltration
import Langlands.Representation.Filtration.Precomposition

/-! Actual native support-image grades of full smooth induction. -/

noncomputable section
open CategoryTheory

namespace Langlands.Geometric

universe uR uG uV

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  [TopologicalSpace G] [NonarchimedeanGroup G]

/-- The full smooth induced representation functor on smooth covariance data. -/
def fullSmoothInductionRepFunctor (P : Subgroup G) :
    SmoothRep.{uR, uG, uV} R P ⥤ Rep.{max uG uV} R G :=
  SmoothRep.toRep ⋙ Induction.smoothInductionFunctor P ⋙ SmoothRep.toRep

namespace OrderedDoubleCosets

variable {P Q : Subgroup G} {n : ℕ}

/-- The actual support filtration of full smooth induction with smooth inputs. -/
def fullSmoothSupportFiltration (s : OrderedDoubleCosets P Q n) :
    RepFunctorFiltration
      (fullSmoothInductionRepFunctor.{uR, uG, uV} (R := R) P ⋙
        Rep.resFunctor Q.subtype) n :=
  s.rawSmoothSupportFiltration.precomp SmoothRep.toRep

variable (U M : Subgroup G) (hMU : M ≤ Subgroup.normalizer U) (hMQ : M ≤ Q)

/-- The original support subspaces mapped into the ambient native quotient,
then scalar-normalized on the literal output subgroup. -/
def nativeSmoothJacquetSupportFiltration (s : OrderedDoubleCosets P Q n)
    (χ : Induction.SmoothCharacter R M) :
    RepFunctorFiltration
      (fullSmoothInductionRepFunctor.{uR, uG, uV} (R := R) P ⋙
        Jacquet.Localization.functor U 1 M hMU
          (Jacquet.Localization.isInvariant_one U M hMU) ⋙ χ.twistFunctor) n :=
  (Jacquet.Localization.restrictedImageFiltration U 1 M hMU
    (Jacquet.Localization.isInvariant_one U M hMU) Q hMQ
      (s.fullSmoothSupportFiltration (R := R))).twist χ

/-- A native image step consists exactly of classes represented in the same
original support step; normalization leaves this membership condition intact. -/
theorem mem_nativeSmoothJacquetSupportFiltration_step
    (s : OrderedDoubleCosets P Q n) (χ : Induction.SmoothCharacter R M)
    (k : Fin (n + 1)) (A : SmoothRep.{uR, uG, uV} R P)
    (q : Jacquet.Localization.Coinvariants
      ((fullSmoothInductionRepFunctor P).obj A).ρ U 1) :
    q ∈ ((s.nativeSmoothJacquetSupportFiltration U M hMU hMQ χ).step k).obj A ↔
      ∃ f ∈ ((s.fullSmoothSupportFiltration (R := R)).step k).obj A,
        Jacquet.Localization.mk ((fullSmoothInductionRepFunctor P).obj A).ρ U 1 f = q :=
  Iff.rfl

variable [LocallyCompactSpace G] [T2Space G]
  [SigmaCompactSpace G] [CompactSpace (Induction.LeftQuotient P)]

/-- The actual successive quotient of full smooth support is the compact
induction of the same orbit stabilizer representation. -/
def fullSmoothSupportGradedOrbitIso
    (hP : IsClosed (P : Set G)) (hQ : IsClosed (Q : Set G))
    (s : OrderedDoubleCosets P Q n) (i : Fin n) :
    (s.fullSmoothSupportFiltration (R := R)).graded i ≅
      orbitPiece.{uR, uG, uV} (R := R) P Q (s.representative i) :=
  (Functor.isoWhiskerLeft SmoothRep.toRep
    (s.rawSupportGradedCompactSmoothIso (R := R) i)).symm ≪≫
      s.coefficientSupportGradedOrbitIso hP hQ i

variable [Algebra ℂ R]
  (hUQ : U ≤ Q) (hU : Jacquet.Localization.IsLimitOfCompactSubgroups U)

set_option maxHeartbeats 800000 in
/-- Each original native, normalized support-image grade of full smooth
induction is the normalized native quotient of its actual compact orbit piece. -/
def nativeSmoothJacquetSupportGradedOrbitIso
    (hP : IsClosed (P : Set G)) (hQ : IsClosed (Q : Set G))
    (s : OrderedDoubleCosets P Q n) (χ : Induction.SmoothCharacter R M) (i : Fin n) :
    (s.nativeSmoothJacquetSupportFiltration U M hMU hMQ χ).graded i ≅
      orbitPiece.{uR, uG, uV} (R := R) P Q (s.representative i) ⋙
        Jacquet.Localization.Coefficient.subgroupFunctor U M hMU Q hUQ hMQ ⋙
          χ.twistFunctor :=
  Jacquet.Localization.Coefficient.twistedRestrictedImageFiltrationGradedIso
    U M hMU Q hUQ hMQ hU
    (fun _ => Induction.smoothInduced_smooth _ _)
    (s.fullSmoothSupportFiltration (R := R)) χ i ≪≫
      Functor.isoWhiskerRight
        (s.fullSmoothSupportGradedOrbitIso hP hQ i)
        (Jacquet.Localization.Coefficient.subgroupFunctor U M hMU Q hUQ hMQ ⋙
          χ.twistFunctor)

end OrderedDoubleCosets
end Langlands.Geometric
