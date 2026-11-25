import Langlands.Geometry.Building.DoubleRootTraceZeroCoordinates
import Langlands.Geometry.Building.RootUnitaryHeisenbergSeparation
import Langlands.GroupScheme.Rational.RootPartnerCharacterNorm
import Langlands.GroupScheme.Rational.RootPartnerCharacterSeparation
import Langlands.GroupScheme.Rational.MultipliableRootNoncommutation

/-! # Heisenberg separation data from actual root partners -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.Geometry.Building

open Langlands.GroupScheme Langlands.GroupScheme.RelativeRoot

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (f : S ⟶ T) (j : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k L
local notation "G_L" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) G
local notation "T_L" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "j_L" => CategoryTheory.Functor.map (GroupScheme.baseChange b) j

private local instance : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

attribute [local instance] rootsGaloisAction

/-- The splitting field receives all embeddings of a root stabilizer field. -/
theorem card_rootOrbitField_embeddings [FiniteDimensional k L] [IsGalois k L]
    (β : roots (T := T_L) (G := G_L) j_L) :
    Nat.card (rootOrbitField k L j β →ₐ[k] L) = Module.finrank k (rootOrbitField k L j β) := by
  rw [IntermediateField.finrank_eq_fixingSubgroup_index,
    RootPartnerFields.fixingSubgroup_rootOrbitField]
  exact (Nat.card_congr (Langlands.Algebra.FiniteGaloisOrbits.quotientEmbeddingEquiv k L
    (MulAction.stabilizer (L ≃ₐ[k] L) β))).symm

/-- Trace-zero elements of a quadratic tower are stable under scalars from
its lowest field. -/
theorem traceZero_smul_mem (F E : Type u) [Field F] [Field E]
    [Algebra k F] [Algebra F E] [Algebra k E] [IsScalarTower k F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
    (c : k) (w : SU3Root.Parameters.traceZero (SU3Root.fieldInvolution F E)) :
    c • (w : E) ∈ SU3Root.Parameters.traceZero (SU3Root.fieldInvolution F E) := by
  change c • (w : E) + (SU3Root.conjugation F E).restrictScalars k (c • (w : E)) = 0
  rw [map_smul, ← smul_add]
  change c • ((w : E) + SU3Root.conjugation F E (w : E)) = 0
  rw [show (w : E) + SU3Root.conjugation F E (w : E) = 0 from w.property, smul_zero]

variable [FiniteDimensional k L] [IsGalois k L] [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom]
  [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
  {a : characterLattice S}
  {U U₂ : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom U.X.hom] [IsAffineHom U₂.X.hom]
  {jU : U ⟶ G} {hjU : (subgroup (CommGroupScheme.groupHom f ≫ j) a).IsRepresentedBy jU}
  {j₂ : U₂ ⟶ G} {hj₂ : (subgroup (CommGroupScheme.groupHom f ≫ j) (2 • a)).IsRepresentedBy j₂}

/-- Existence of field-valued Heisenberg separation data for the actual
represented root quotient and doubled root group. -/
def HasActualRootHeisenbergSeparationData
    (C : DoubleRootCommutatorPairing (CommGroupScheme.groupHom f ≫ j) a hjU hj₂)
    {hfix : ∀ (X : Over (Spec (CommRingCat.of k))) (z : X ⟶ T.toGrp.X) (t : X ⟶ S.X),
      (AutomorphicAction.conjugation j).act z (t ≫ (CommGroupScheme.groupHom f ≫ j).hom.hom) =
        t ≫ (CommGroupScheme.groupHom f ≫ j).hom.hom}
    (N : EquivariantHeisenbergNormalForm C (AutomorphicAction.conjugation j) hfix) : Prop :=
  Nonempty (HeisenbergUnitarySeparationData C N (CommGroupScheme.groupHom f))

/-- Actual partner roots provide the fields, both coordinates and all the
bilinear, action, nonsymmetry and character-separation laws. -/
theorem hasActualRootHeisenbergSeparationData_of_partner [Infinite k]
    (C : DoubleRootCommutatorPairing (CommGroupScheme.groupHom f ≫ j) a hjU hj₂)
    [IsAffineHom C.V.X.hom]
    {hfix : ∀ (X : Over (Spec (CommRingCat.of k))) (z : X ⟶ T.toGrp.X) (t : X ⟶ S.X),
      (AutomorphicAction.conjugation j).act z (t ≫ (CommGroupScheme.groupHom f ≫ j).hom.hom) =
        t ≫ (CommGroupScheme.groupHom f ≫ j).hom.hom}
    (N : EquivariantHeisenbergNormalForm C (AutomorphicAction.conjugation j) hfix)
    (hG : IsConnectedReductive G) (hjc : IsClosedSubgroup j) (hj : IsMaximalTorus j)
    (hf : IsMaximalSplitTorus (CommGroupScheme.groupHom f ≫ j))
    (hcent : (torusCentralizer (CommGroupScheme.groupHom f ≫ j)).IsRepresentedBy j)
    (hT : IsSplitTorus (T_L).toGrp)
    {J : Type u} [Finite J]
    {P : RootDatum J (characterLattice T_L) (cocharacterLattice T_L)}
    (hP : IsRootDatumOf (T := T_L) j_L P)
    (ha : a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (h2a : 2 • a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (beta beta' mu0 : roots (T := T_L) (G := G_L) j_L)
    (hpartner : RootPartnerFields.IsRootPartner k L j beta beta')
    (hmu : mu0.val = beta.val + beta'.val)
    (hbeta : beta ∈ rootRestrictionFiber k L j f a)
    (hmuFiber : mu0 ∈ rootRestrictionFiber k L j f (2 • a)) :
    HasActualRootHeisenbergSeparationData k f j C N := by
  classical
  let hS : IsSplitTorus S.toGrp := hf.1.1
  let : IsAffineHom S.toGrp.X.hom := hS.isAffineHom
  let : IsAffine S.toGrp.X.left := isAffine_of_isAffineHom S.toGrp.X.hom
  let : IsAffine T.toGrp.X.left := isAffine_of_isAffineHom T.toGrp.X.hom
  have ha0 : a ≠ 0 := (mem_relativeRoots.mp ha).1
  have hjL : IsClosedImmersion (j_L).hom.hom.left := IsClosedSubgroup.baseChange b hjc
  have hzero := root_restrict_ne_zero_of_torusCentralizer k L f j hS hT hcent
  have hne : ∀ gamma : roots (T := T_L) (G := G_L) j_L,
      CharacterAveraging.galoisOrbitSum k L T gamma.val ≠ 0 := fun gamma =>
    galoisOrbitSum_ne_zero_of_restrict_ne_zero k L f hS (hzero gamma)
  let F := rootOrbitField k L j mu0
  let E := rootOrbitField k L j beta
  have hle : F ≤ E := RootPartnerFields.rootOrbitField_le k L hT hjL hP hne hpartner hmu
  let : Algebra F E := Langlands.Algebra.QuadraticFixedFields.nestedAlgebra F E hle
  let : IsScalarTower F E L :=
    Langlands.Algebra.QuadraticFixedFields.nestedAlgebra_isScalarTower F E hle
  let : IsScalarTower k F E := Langlands.Algebra.QuadraticFixedFields.isScalarTower_base F E
  let : Algebra.IsQuadraticExtension F E :=
    RootPartnerFields.isQuadraticExtension k L hT hjL hP hne hpartner hmu
  let : Algebra.IsSeparable F E := RootPartnerFields.isSeparable k L
  have horbit := rootOrbit_eq_restrictionFiber_of_torusCentralizer k L f j hf hjc hcent hT hP a hbeta
  have horbit2 := rootOrbit_eq_restrictionFiber_of_torusCentralizer k L f j hf hjc hcent hT hP
    (2 • a) hmuFiber
  let first : Multiplicative E ≃* rationalPoints C.V :=
    quotientFieldEquiv k L f j C hG hj hS hT ha0 hhigh beta horbit
  let value (z : rationalPoints T.toGrp) : E :=
    (rationalCharacterEval (rootOrbitCharacter k L j beta)
      (GaloisPointComparison.rationalExtend k E T.toGrp z) : E)
  have hnorm : ∀ z : rationalPoints T.toGrp,
      algebraMap F E (rationalCharacterEval (rootOrbitCharacter k L j mu0)
        (GaloisPointComparison.rationalExtend k F T.toGrp z) : F) =
      value z * SU3Root.conjugation F E (value z) :=
    RootPartnerFields.hasCharacterNormValues k L j hT hjL hP hne hpartner hmu
  obtain ⟨second, hsecond, hsecondAct⟩ := hasDoubleRootTraceZeroCoordinates k L f j mu0 E hj₂
    hG hj hS hT ha0 hhigh horbit2 hfix value hnorm
  let form (x y : E) : E :=
    (Multiplicative.toAdd (second.symm
      (lift (first (Multiplicative.ofAdd x)) (first (Multiplicative.ofAdd y)) ≫ N.cocycle))).1
  have hcocycle : ∀ x y : E,
      (Multiplicative.toAdd (second.symm
        (lift (first (Multiplicative.ofAdd x)) (first (Multiplicative.ofAdd y)) ≫ N.cocycle))).1 =
      form x y := fun _ _ => rfl
  have hfirst := quotientFieldEquiv_smul k L f j C hG hj hS hT ha0 hhigh beta horbit
  have hH := traceZero_smul_mem k F E
  have hncomm := MultipliableRootNoncommutation.not_pointsCommute k L f j hG hjc hf hcent hT
    hP ha h2a hhigh hjU
  obtain ⟨X, g, g', hgg'⟩ : ∃ (X : Over (Spec (CommRingCat.of k))) (g g' : X ⟶ U.X),
      ¬ Commute g g' := by
    simpa only [PointsCommute, not_forall] using hncomm
  refine ⟨{
    base := F
    extension := E
    first := first
    second := second
    form := form
    cocycle_eq := hcocycle
    form_smul_left := HeisenbergNormalForm.form_smul_left_of_lie hS ha0 hhigh N.toHeisenbergNormalForm
      first second form hcocycle hH hfirst hsecond
    form_smul_right := HeisenbergNormalForm.form_smul_right_of_lie hS ha0 hhigh N.toHeisenbergNormalForm
      first second form hcocycle hH hfirst hsecond
    form_nonsymm := N.toHeisenbergNormalForm.exists_form_ne_swap hS ha0 hhigh first second
      form hcocycle g g' hgg'
    character := rootOrbitCharacter k L j beta
    restriction := characterRestrict_rootOrbitCharacter k L j f a hbeta
    first_act := quotientFieldEquiv_act_character k L f j C hG hj hS hT ha0 hhigh beta horbit hfix
    second_act := hsecondAct
    splitting := L
    card_embeddings := card_rootOrbitField_embeddings k L j beta
    separation := RootPartnerFields.hasSeparatingCharacterValues k L j hT hjL hP hne hpartner hmu
  }⟩

/-- Structural multipliable-root hypotheses supply their own actual partner
roots, quadratic fields, coordinates and separation data. -/
theorem hasActualRootHeisenbergSeparationData [Infinite k]
    (C : DoubleRootCommutatorPairing (CommGroupScheme.groupHom f ≫ j) a hjU hj₂)
    [IsAffineHom C.V.X.hom]
    {hfix : ∀ (X : Over (Spec (CommRingCat.of k))) (z : X ⟶ T.toGrp.X) (t : X ⟶ S.X),
      (AutomorphicAction.conjugation j).act z (t ≫ (CommGroupScheme.groupHom f ≫ j).hom.hom) =
        t ≫ (CommGroupScheme.groupHom f ≫ j).hom.hom}
    (N : EquivariantHeisenbergNormalForm C (AutomorphicAction.conjugation j) hfix)
    (hG : IsConnectedReductive G) (hjc : IsClosedSubgroup j)
    (hf : IsMaximalSplitTorus (CommGroupScheme.groupHom f ≫ j))
    (hcent : (torusCentralizer (CommGroupScheme.groupHom f ≫ j)).IsRepresentedBy j)
    (hT : IsSplitTorus (T_L).toGrp)
    {J : Type u} [Finite J]
    {P : RootDatum J (characterLattice T_L) (cocharacterLattice T_L)}
    (hP : IsRootDatumOf (T := T_L) j_L P)
    (ha : a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (h2a : 2 • a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots (CommGroupScheme.groupHom f ≫ j)) :
    HasActualRootHeisenbergSeparationData k f j C N := by
  classical
  have hS : IsSplitTorus S.toGrp := hf.1.1
  have hzero := root_restrict_ne_zero_of_torusCentralizer k L f j hS hT hcent
  have hTt : IsTorus T.toGrp := ⟨L, inferInstance, inferInstance, hT⟩
  let : IsAffine T.X.left := isAffine_of_isAffineHom T.toGrp.X.hom
  have hself : torusCentralizer j = SubgroupFunctor.range j :=
    le_antisymm ((torusCentralizer_le_of_factor j (CommGroupScheme.groupHom f ≫ j)
      (CommGroupScheme.groupHom f) rfl).trans hcent.2.symm.le) (range_le_torusCentralizer j)
  have hj : IsMaximalTorus j := isMaximalTorus_of_torusCentralizer_eq hTt hjc hself
  have hjL : IsMaximalTorus (T := T_L) j_L :=
    isMaximalTorus_baseChange_of_torusCentralizer_eq L hTt hjc hself
  let : Algebra.IsAlgebraic k L := Algebra.IsAlgebraic.of_finite k L
  have hGL : IsConnectedReductive G_L := hG.baseChange_of_algebraicExtension (K := L)
  have hroot : ∀ m : J, P.root m ∈ roots (T := T_L) (G := G_L) j_L :=
    RootPartnerFields.root_mem_roots k L hP
  have hred : ∀ r : J, P.root r + P.root r ∉ Set.range P.root := by
    intro r h
    apply RootPairNoncommutation.hasNoHigherRoots hGL hT hjL hP r 2 le_rfl
    rw [two_nsmul, relativeRoots_eq_roots, ← hP.2.1]
    exact h
  obtain ⟨r, r', sigma, ⟨hr, hr', hpair, hsum⟩, hsigma, -⟩ :=
    MultipliableRootNoncommutation.exists_partner k L f j hS
      (hf.of_comp hjc).isLargestSplitSubtorus hT (IsClosedSubgroup.baseChange b hjc) hP
      hzero hred ha h2a
  let beta : roots (T := T_L) (G := G_L) j_L := ⟨P.root r, hroot r⟩
  let beta' : roots (T := T_L) (G := G_L) j_L := ⟨P.root r', hroot r'⟩
  have hsumRoot : P.root r + P.root r' ∈ roots (T := T_L) (G := G_L) j_L := by
    rw [← hP.2.1]
    exact hsum
  let mu0 : roots (T := T_L) (G := G_L) j_L := ⟨P.root r + P.root r', hsumRoot⟩
  have hpartner : RootPartnerFields.IsRootPartner k L j beta beta' := by
    refine ⟨⟨sigma, Subtype.ext hsigma⟩, ?_, hsumRoot⟩
    intro h
    have heq : r' = r := P.root.injective (congrArg Subtype.val h)
    rw [heq, RootPairing.pairing_same] at hpair
    norm_num at hpair
  have hmuFiber : mu0 ∈ rootRestrictionFiber k L j f (2 • a) := by
    change (CommGroupScheme.baseChange b).map f ≫ (P.root r + P.root r') =
      characterLattice.baseChange b S (2 • a)
    simp only [Preadditive.comp_add, hr, hr', two_nsmul, map_add]
  exact hasActualRootHeisenbergSeparationData_of_partner k L f j C N hG hjc hj hf hcent
    hT hP ha h2a hhigh beta beta' mu0 hpartner rfl hr hmuFiber

end Langlands.Geometry.Building
