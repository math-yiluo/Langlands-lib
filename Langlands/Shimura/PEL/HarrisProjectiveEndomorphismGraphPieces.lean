import Langlands.AbelianScheme.RelativeEndomorphismAffineHomSchemePieces

/-! # Affine endomorphism pieces with their graph polynomial test -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite
open Langlands.AbelianScheme Langlands.GroupScheme.Cartier

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

namespace Langlands.Shimura.PEL

open AbelianScheme.AffineHomSchemePieces

variable {R : Type u} [CommRing R] (B : AbelianScheme (Spec (.of R)))
    (L : B.X.left.Modules)

local notation "S" => Spec (CommRingCat.of R)
local notation "Affines" => ObjectProperty.ι (fun T : Over S => IsAffine T.left)
local notation "endFunctor" =>
  relativeHomFunctor B.toCommGroupScheme B.toCommGroupScheme ⋙ forget AddCommGrpCat
local notation "EndAt" => RelativeHom B.toCommGroupScheme B.toCommGroupScheme

/-- The actual affine endomorphism representative with its disjoint open
pieces, indexed by the graph Hilbert polynomial for the specified invertible
module. The pointwise characterization uses the same representing comparison. -/
structure ProjectiveEndomorphismGraphPieces where
  scheme : Over S
  separated : IsSeparated scheme.hom
  locallyOfFiniteType : LocallyOfFiniteType scheme.hom
  formallyUnramified : FormallyUnramified scheme.hom
  comparison : (Affines).op ⋙ endFunctor ≅ (Affines).op ⋙ yoneda.obj scheme
  opens : Polynomial ℚ → scheme.left.Opens
  disjoint : Pairwise (Function.onFun Disjoint opens)
  cover : (⨆ p, opens p) = ⊤
  closed (p : Polynomial ℚ) : IsClosed (opens p : Set scheme.left)
  quasiCompact (p : Polynomial ℚ) : QuasiCompact ((opens p).ι ≫ scheme.hom)
  range_subset_iff (p : Polynomial ℚ)
      (R' : Type u) [CommRing R'] (s : Spec (.of R') ⟶ S)
      (χ : EndAt (Over.mk s)) :
    Set.range ((comparison.hom.app
      (op ⟨Over.mk s, inferInstanceAs (IsAffine (Spec (.of R')))⟩)) χ).left ⊆ opens p ↔
      ∀ (K : Type u) [Field K] [IsAlgClosed K] (sk : R' →+* K), ∃ n₀ : ℕ,
        ∀ n : ℕ, n₀ ≤ n →
          ((Scheme.Modules.geomFibreH0Finrank (pullback.snd B.X.hom s)
            (Nat.rec (motive := fun _ => (pullback B.X.hom s).Modules)
              (𝟙_ (pullback B.X.hom s).Modules)
              (fun _ M => M ⊗
                ((Scheme.Modules.pullback (pullback.fst B.X.hom s)).obj L ⊗
                  (Scheme.Modules.pullback (fstMap χ)).obj L)) n) K sk : ℕ) : ℚ) =
            p.eval (n : ℚ)

private theorem natIso_app_spec_left
    {H : Scheme.{u}} {πH : H ⟶ S}
    {pt : ∀ (R' : Type u) [CommRing R'] (s : Spec (.of R') ⟶ S)
      (φ : pullback B.X.hom s ⟶ B.X.left), φ ≫ B.X.hom = pullback.snd B.X.hom s ≫ s →
        NeronModelInfra.SchemeHomOver s πH}
    (hnat : PtNat (A := B) pt) (hsurj : PtSurj (A := B) pt) (hinj : PtInj (A := B) pt)
    {R' : Type u} [CommRing R'] (s : Spec (.of R') ⟶ S) (χ : EndAt (Over.mk s)) :
    (((natIso (A := B) hnat hsurj hinj).hom.app
      (op ⟨Over.mk s, inferInstanceAs (IsAffine (Spec (.of R')))⟩)) χ).left =
      (homPt pt s χ).1 := by
  let T := Over.mk s
  let : IsAffine T.left := inferInstanceAs (IsAffine (Spec (.of R')))
  change (homEquiv hsurj hinj T χ).left = _
  rw [AffineHomSchemePieces.homEquiv_left, homPt_restrict hnat (ofSpec T) χ]
  change (isoSpec T).hom ≫ (isoSpec T).inv ≫ (homPt pt s χ).1 = _
  rw [Iso.hom_inv_id_assoc]

variable (hL : Scheme.Modules.IsInvertibleFLT L)
    (hEmbedding : Scheme.Modules.ClosedImmersionBySections L B.X.hom)

include hL hEmbedding in
private theorem exists_projectiveEndomorphismGraphPieces :
    Nonempty (ProjectiveEndomorphismGraphPieces B L) := by
  obtain ⟨H, πH, pt, hnat, hsurj, hinj, hsep, hlft, -, hunram, U, hdisjoint, hcover, hU⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections
      R B.X.hom B.X.hom (groupLaw B) (groupLaw B) (groupLaw_isCommutative B)
      (groupLaw_isCommutative B) (propertyBundle B) (propertyBundle B) L hL hEmbedding L hL hEmbedding
  refine ⟨{
    scheme := Over.mk πH
    separated := hsep
    locallyOfFiniteType := hlft
    formallyUnramified := hunram
    comparison := natIso (pt := pt) hnat hsurj hinj
    opens := U
    disjoint := hdisjoint
    cover := hcover
    closed := fun p => (hU p).1
    quasiCompact := fun p => (hU p).2.1
    range_subset_iff := ?_ }⟩
  intro p R' _ s χ
  rw [natIso_app_spec_left B hnat hsurj hinj]
  exact (hU p).2.2 R' s (fstMap χ) (fstMap_hom χ) (isFLTHom_fstMap B s χ)

/-- Use the specified projective embedding by sections to retain the
individual polynomial labels in the actual relative Hom construction. -/
def projectiveEndomorphismGraphPieces : ProjectiveEndomorphismGraphPieces B L :=
  Classical.choice (exists_projectiveEndomorphismGraphPieces B L hL hEmbedding)

end Langlands.Shimura.PEL
