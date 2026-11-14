import Langlands.BruhatTits.IntegralModels.OrderedIntegralOpenCellFamily
import Langlands.GroupScheme.IntegralModel.IntegralPointIsoCriterion
import Langlands.GroupScheme.IntegralModel.OrderedCellLemmas
import Langlands.GroupScheme.IntegralModel.HenselianReduction
import Langlands.GroupScheme.KernelOrderedProductChart
import Langlands.GroupScheme.ProductProperties
import Langlands.GroupScheme.Dynamic.BaseTripleCell
import Langlands.GroupScheme.Dynamic.RelativeCentralizerComparison
import Langlands.GroupScheme.Rational.SplitTorusCentralizerReduction
import Langlands.Geometry.Building.GenericOrderedFixerFactors

/-! # Ordered integral open cells over the maximal unramified integers -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels

namespace OrderedIntegralOpenCell

/-! ### Finite products of smooth affine group schemes -/

section Products

variable {S : Scheme.{u}} {n : ℕ}

/-- Finite products over `Fin n` inherit stable properties of structure morphisms. -/
theorem prop_finiteProduct_hom (P : MorphismProperty Scheme.{u}) [P.IsStableUnderComposition]
    [P.IsStableUnderBaseChange] [P.ContainsIdentities] [P.RespectsIso]
    (A : Fin n → GroupScheme S) (hA : ∀ r, P (A r).X.hom) : P (∏ᶜ A).X.hom := by
  have h := prop_pi_hom P (fun r : ULift.{u} (Fin n) => A r.down) (fun r => hA r.down)
  let e := RelativeRoot.finiteProductUniverseIso A
  rw [← Over.w e.inv]
  exact (MorphismProperty.cancel_left_of_respectsIso P e.inv.left _).mpr h

end Products

/-! ### Integral cocharacters of an integral split torus -/

section Cocharacters

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {S : CommGroupScheme (Spec (CommRingCat.of K))} {G : GroupScheme (Spec (CommRingCat.of K))}
  {i : S.toGrp ⟶ G} {N : IntegralModel R K G} (A : IntegralSplitTorusData N i)

/-- The actual integral cocharacter with the prescribed generic cocharacter. -/
def integralCocharacter (ν : cocharacterLattice S) : cocharacterLattice A.torus :=
  (cocharacterLattice.baseChangeEquiv (Spec.algebraMap R K) A.torus A.isSplit).symm
    ((cocharacterLattice.congr A.genericIso).symm ν)

theorem generic_integralCocharacter (ν : cocharacterLattice S) :
    cocharacterLattice.congr A.genericIso
      (cocharacterLattice.baseChange (Spec.algebraMap R K) A.torus
        (integralCocharacter A ν)) = ν := by
  change cocharacterLattice.congr A.genericIso
    (cocharacterLattice.baseChangeEquiv (Spec.algebraMap R K) A.torus A.isSplit
      ((cocharacterLattice.baseChangeEquiv (Spec.algebraMap R K) A.torus A.isSplit).symm
        ((cocharacterLattice.congr A.genericIso).symm ν))) = ν
  rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

theorem integralCocharacter_neg (ν : cocharacterLattice S) :
    integralCocharacter A (-ν) = -integralCocharacter A ν := by
  unfold integralCocharacter
  rw [(cocharacterLattice.congr A.genericIso).symm.map_neg,
    (cocharacterLattice.baseChangeEquiv (Spec.algebraMap R K) A.torus A.isSplit).symm.map_neg]

theorem latticePairing_integralCharacter_integralCocharacter (a : characterLattice S)
    (ν : cocharacterLattice S) :
    latticePairing A.torus (A.integralCharacter a) (integralCocharacter A ν) =
      latticePairing S a ν := by
  rw [← latticePairing_baseChange (Spec.algebraMap R K) A.torus,
    ← latticePairing_congr A.genericIso, A.generic_integralCharacter,
    generic_integralCocharacter]

/-- The integral cocharacter of the ambient model. -/
def integralCocharacterHom (ν : cocharacterLattice S) :
    (Gm (Spec (CommRingCat.of R))).toGrp ⟶ N.group :=
  CommGroupScheme.groupHom (integralCocharacter A ν) ≫ A.inclusion

theorem baseChange_integralCocharacterHom (ν : cocharacterLattice S) :
    Dynamic.baseChangeCocharacter (Spec.algebraMap R K) (integralCocharacterHom A ν) ≫
      N.genericIso.hom = CommGroupScheme.groupHom ν ≫ i := by
  rw [integralCocharacterHom, Dynamic.baseChangeCocharacter_comp, Category.assoc]
  change Dynamic.baseChangeCocharacter _ _ ≫ N.genericHom A.inclusion = _
  rw [A.generic_comm, ← cocharacterLattice.groupHom_baseChange_dynamic, ← Category.assoc]
  conv_rhs => rw [← generic_integralCocharacter A ν]
  rfl

theorem integralCocharacterHom_neg (ν : cocharacterLattice S) :
    integralCocharacterHom A (-ν) =
      Dynamic.oppositeCocharacter (integralCocharacterHom A ν) := by
  rw [integralCocharacterHom, integralCocharacter_neg,
    groupHom_neg_comp_eq_oppositeCocharacter_overBase]
  rfl

/-- The generic fibre of a representative of the integral dynamic unipotent
subgroup represents the generic dynamic unipotent subgroup. -/
theorem isRepresentedBy_genericHom_unipotent (ν : cocharacterLattice S)
    {U : GroupScheme (Spec (CommRingCat.of R))} {jU : U ⟶ N.group}
    (hjU : (Dynamic.unipotent (integralCocharacterHom A ν)).IsRepresentedBy jU) :
    (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy
      (N.genericHom jU) := by
  have h := hjU.baseChange (Spec.algebraMap R K)
  rw [← Dynamic.unipotent_baseChange] at h
  have h2 := h.comp_iso N.genericIso
  rw [Dynamic.unipotent_eq_comap_of_iso _ N.genericIso, ← SubgroupFunctor.comap_comp,
    Iso.inv_hom_id, SubgroupFunctor.comap_id, baseChange_integralCocharacterHom] at h2
  exact h2

/-- The generic fibre of a representative of the integral dynamic centralizer
represents the generic dynamic centralizer. -/
theorem isRepresentedBy_genericHom_centralizer (ν : cocharacterLattice S)
    {Z : GroupScheme (Spec (CommRingCat.of R))} {jZ : Z ⟶ N.group}
    (hjZ : (Dynamic.centralizer (integralCocharacterHom A ν)).IsRepresentedBy jZ) :
    (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy
      (N.genericHom jZ) := by
  have h := hjZ.baseChange (Spec.algebraMap R K)
  rw [← Dynamic.centralizer_baseChange] at h
  have h2 := h.comp_iso N.genericIso
  rw [Dynamic.centralizer_eq_comap_of_iso _ N.genericIso, ← SubgroupFunctor.comap_comp,
    Iso.inv_hom_id, SubgroupFunctor.comap_id, baseChange_integralCocharacterHom] at h2
  exact h2

end Cocharacters

/-! ### Integral ordered products from generic decompositions and integral factors -/

section RootProducts

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
  [Field K] [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))} (N : IntegralModel R K G)

omit [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [IsSepClosed (IsLocalRing.ResidueField R)] in
/-- The generic point of an integral section of a subgroup, through its inclusion. -/
theorem integralPointMap_comp {U : GroupScheme (Spec (CommRingCat.of R))} (jU : U ⟶ N.group)
    (y : rationalPoints U) :
    N.integralPointMap (y ≫ jU.hom.hom) =
      baseChangeSectionHom (Spec.algebraMap R K) U y ≫ (N.genericHom jU).hom.hom := by
  change baseChangeSectionHom (Spec.algebraMap R K) N.group (y ≫ jU.hom.hom) ≫
    N.genericIso.hom.hom.hom = _
  rw [baseChangeSectionHom_naturality, Category.assoc]
  rfl

/-- **Integral ordered products.** Let `f r` be integral factor maps into a
represented integral subgroup `U` of a smooth model. Suppose the generic factors and
generic `U` have unique ordered decompositions, ordered factors of integral generic
points are integral, and integral generic factor points lift to integral sections.
Then the internal ordered multiplication into `U` is an isomorphism. -/
theorem isIso_orderedMultiplication_of_generic {n : ℕ}
    {Hr : Fin n → GroupScheme (Spec (CommRingCat.of R))}
    [hHs : ∀ r, Smooth (Hr r).X.hom] [hHa : ∀ r, IsAffineHom (Hr r).X.hom]
    (f : ∀ r, Hr r ⟶ N.group)
    {V : SubgroupFunctor N.group} {U : GroupScheme (Spec (CommRingCat.of R))}
    {jU : U ⟶ N.group} (hjU : V.IsRepresentedBy jU) [Smooth U.X.hom] [IsAffineHom U.X.hom]
    (hfV : ∀ r, SubgroupFunctor.range (f r) ≤ V)
    {FK : Fin n → SubgroupFunctor G} {VK : SubgroupFunctor G}
    (hfK : ∀ r, (FK r).IsRepresentedBy (N.genericHom (f r)))
    (hUK : VK.IsRepresentedBy (N.genericHom jU))
    (hUD : ∀ (T : Over (Spec (CommRingCat.of K))) (g : T ⟶ G.X), g ∈ VK.carrier T →
        ∃! x : ∀ r, (FK r).carrier T, (List.ofFn fun r => (x r : T ⟶ G.X)).prod = g)
    (hfac : ∀ u : Fin n → rationalPoints G,
        (∀ r, u r ∈ (FK r).carrier (Over.mk (𝟙 _))) →
          (List.ofFn u).prod ∈ N.integralPoints → ∀ r, u r ∈ N.integralPoints)
    (hsec : ∀ (r : Fin n) (g : rationalPoints G), g ∈ N.integralPoints →
        g ∈ (FK r).carrier (Over.mk (𝟙 _)) →
          ∃ s : rationalPoints (Hr r), N.integralPointMap (s ≫ (f r).hom.hom) = g) :
    IsIso (RelativeRoot.orderedMultiplication (fun r => hjU.factorHom (f r) (hfV r))) := by
  let b := Spec.algebraMap R K
  have hP : IsAffineHom (∏ᶜ Hr).X.hom :=
    prop_finiteProduct_hom @IsAffineHom Hr (fun r => hHa r)
  have : MorphismProperty.ContainsIdentities @Smooth := ⟨fun _ => inferInstance⟩
  have hS : Smooth (∏ᶜ Hr).X.hom := prop_finiteProduct_hom @Smooth Hr (fun r => hHs r)
  have : IsAffine (∏ᶜ Hr).X.left := isAffine_of_isAffineHom (∏ᶜ Hr).X.hom
  have : IsAffine U.X.left := isAffine_of_isAffineHom U.X.hom
  have hm : Mono jU.hom.hom := hjU.1
  have hgen (r : Fin n) : N.genericHom (f r) =
      (GroupScheme.baseChange b).map (hjU.factorHom (f r) (hfV r)) ≫ N.genericHom jU := by
    unfold IntegralModel.genericHom
    rw [← Category.assoc, ← Functor.map_comp,
      SubgroupFunctor.IsRepresentedBy.factorHom_comp]
  have hfK' (r : Fin n) : SubgroupFunctor.range (N.genericHom (f r)) ≤ VK := by
    rw [← hUK.2, hgen r]
    exact SubgroupFunctor.range_comp_le _ _
  have hK : IsIso ((Over.pullback b).map
      (RelativeRoot.orderedMultiplication (fun r => hjU.factorHom (f r) (hfV r)))) := by
    have hiso : IsIso (RelativeRoot.orderedMultiplication
        (fun r => hUK.factorHom (N.genericHom (f r)) (hfK' r))) :=
      (RelativeRoot.isIso_orderedMultiplication_factorHom_iff hUK _ hfK hfK').mpr hUD
    have heq : (fun r => (GroupScheme.baseChange b).map (hjU.factorHom (f r) (hfV r))) =
        (fun r => hUK.factorHom (N.genericHom (f r)) (hfK' r)) :=
      funext fun r => SubgroupFunctor.IsRepresentedBy.factorHom_unique hUK _ _ (hgen r).symm
    rw [← RelativeRoot.orderedMultiplication_baseChange b, heq]
    infer_instance
  apply IntegralModel.IntegralPointIsoCriterion.isIso_of_isIso_baseChange_of_forall_exists_comp_eq
    (K := K) _ hK
  intro y
  have hgK : N.integralPointMap (y ≫ jU.hom.hom) ∈ VK.carrier (Over.mk (𝟙 _)) := by
    rw [integralPointMap_comp, ← hUK.2]
    exact ⟨_, rfl⟩
  obtain ⟨u, hu, -⟩ := hUD _ _ hgK
  have hint : ∀ r, (u r : rationalPoints G) ∈ N.integralPoints :=
    hfac (fun r => u r) (fun r => (u r).2) (by rw [hu]; exact ⟨_, rfl⟩)
  choose s hs using fun r => hsec r (u r) (hint r) (u r).2
  refine ⟨(RelativeRoot.finiteProductPointsEquiv Hr _).symm s, ?_⟩
  apply hm.right_cancellation
  rw [Category.assoc, RelativeRoot.orderedMultiplication_factorHom hjU f hfV,
    RelativeRoot.finiteProductPointsEquiv_symm_orderedMultiplication]
  apply N.integralPointMap_injective
  change N.integralPointMap (List.ofFn fun r => s r ≫ (f r).hom.hom).prod = _
  rw [map_list_prod, List.map_ofFn]
  rw [← hu]
  congr 1
  apply congrArg List.ofFn
  funext r
  exact hs r

omit [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [IsSepClosed (IsLocalRing.ResidueField R)] in
/-- A closed integral subgroup comparison into a flat representative is an
isomorphism when both generic fibres represent the same subgroup functor. -/
theorem isIso_factorHom_of_generic {Z₁ Z₂ : GroupScheme (Spec (CommRingCat.of R))}
    (j₁ : Z₁ ⟶ N.group) (j₂ : Z₂ ⟶ N.group) [IsClosedImmersion j₁.hom.hom.left]
    [IsClosedImmersion j₂.hom.hom.left] [Flat Z₂.X.hom] {W : SubgroupFunctor N.group}
    (h₂ : W.IsRepresentedBy j₂) (h₁₂ : SubgroupFunctor.range j₁ ≤ W)
    {FK : SubgroupFunctor G} (hK₁ : FK.IsRepresentedBy (N.genericHom j₁))
    (hK₂ : FK.IsRepresentedBy (N.genericHom j₂)) :
    IsIso (h₂.factorHom j₁ h₁₂).hom.hom := by
  have hcomp : h₂.factorHom j₁ h₁₂ ≫ j₂ = j₁ :=
    SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _
  have : IsClosedImmersion (h₂.factorHom j₁ h₁₂).hom.hom.left := by
    have : IsClosedImmersion ((h₂.factorHom j₁ h₁₂).hom.hom.left ≫ j₂.hom.hom.left) := by
      rw [← Over.comp_left, ← Grp.comp_hom_hom, hcomp]
      infer_instance
    exact IsClosedImmersion.of_comp_isClosedImmersion _ j₂.hom.hom.left
  apply isIso_of_isClosedImmersion_of_isIso_pullback (K := K)
  have hgen : (GroupScheme.baseChange (Spec.algebraMap R K)).map (h₂.factorHom j₁ h₁₂) ≫
      N.genericHom j₂ = N.genericHom j₁ := by
    unfold IntegralModel.genericHom
    rw [← Category.assoc, ← Functor.map_comp, hcomp]
  have heq : (GroupScheme.baseChange (Spec.algebraMap R K)).map (h₂.factorHom j₁ h₁₂) =
      (hK₁.isoOfIsRepresentedBy hK₂).hom :=
    hK₂.hom_ext (hgen.trans (hK₁.isoOfIsRepresentedBy_hom_comp hK₂).symm)
  change IsIso ((GroupScheme.baseChange (Spec.algebraMap R K)).map
    (h₂.factorHom j₁ h₁₂)).hom.hom
  rw [heq]
  exact (inferInstance : IsIso ((Grp.forget _).mapIso (hK₁.isoOfIsRepresentedBy hK₂)).hom)

end RootProducts

/-! ### Splitting a negative/middle/positive ordered product -/

section Split

variable {B : Scheme.{u}} {G : GroupScheme B} {n₁ n₂ : ℕ}
  {H : Fin (n₁ + (n₂ + 1)) → GroupScheme B}

variable (H) in
/-- The negative block of factors. -/
abbrev negFactor : Fin n₁ → GroupScheme B := fun r => H (Fin.castAdd (n₂ + 1) r)

variable (H) in
/-- The positive block of factors. -/
abbrev posFactor : Fin n₂ → GroupScheme B := fun r => H (Fin.natAdd n₁ r.succ)

variable (H) in
/-- The target of the splitting isomorphism. -/
abbrev splitObj : Over B :=
  (∏ᶜ negFactor H).X ⊗ ((H (Fin.natAdd n₁ 0)).X ⊗ (∏ᶜ posFactor H).X)

variable (H) in
/-- Coordinates of an ordered product split into its three blocks. -/
def splitHom : (∏ᶜ H).X ⟶ splitObj H :=
  lift ((RelativeRoot.finiteProductPointsEquiv (negFactor H) _).symm
      fun r => (Pi.π H (Fin.castAdd (n₂ + 1) r)).hom.hom)
    (lift (Pi.π H (Fin.natAdd n₁ 0)).hom.hom
      ((RelativeRoot.finiteProductPointsEquiv (posFactor H) _).symm
        fun r => (Pi.π H (Fin.natAdd n₁ r.succ)).hom.hom))

variable (H) in
/-- Reassembly of the three blocks. -/
def splitInv : splitObj H ⟶ (∏ᶜ H).X :=
  (RelativeRoot.finiteProductPointsEquiv H _).symm fun i =>
    Fin.addCases (motive := fun i => splitObj H ⟶ (H i).X)
      (fun r => fst _ _ ≫ (Pi.π (negFactor H) r).hom.hom)
      (fun k => Fin.cases (motive := fun k => splitObj H ⟶ (H (Fin.natAdd n₁ k)).X)
        (snd _ _ ≫ fst _ _)
        (fun r => snd _ _ ≫ snd _ _ ≫ (Pi.π (posFactor H) r).hom.hom) k) i

theorem splitHom_splitInv : splitHom H ≫ splitInv H = 𝟙 _ := by
  apply Fan.IsLimit.hom_ext (RelativeRoot.finiteProductIsLimit H)
  intro i
  change (splitHom H ≫ splitInv H) ≫ (Pi.π H i).hom.hom = 𝟙 _ ≫ (Pi.π H i).hom.hom
  rw [Category.assoc, splitInv, RelativeRoot.finiteProductPointsEquiv_symm_π, Category.id_comp]
  induction i using Fin.addCases with
  | left r =>
    simp only [Fin.addCases_left, splitHom, lift_fst_assoc,
      RelativeRoot.finiteProductPointsEquiv_symm_π]
  | right k =>
    simp only [Fin.addCases_right]
    induction k using Fin.cases with
    | zero => simp only [Fin.cases_zero, splitHom, lift_snd_assoc, lift_fst]
    | succ r =>
      simp only [Fin.cases_succ, splitHom, lift_snd_assoc,
        RelativeRoot.finiteProductPointsEquiv_symm_π]

theorem splitInv_splitHom : splitInv H ≫ splitHom H = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, splitHom, lift_fst, Category.id_comp]
    apply Fan.IsLimit.hom_ext (RelativeRoot.finiteProductIsLimit (negFactor H))
    intro r
    change (splitInv H ≫ _) ≫ (Pi.π (negFactor H) r).hom.hom =
      fst _ _ ≫ (Pi.π (negFactor H) r).hom.hom
    rw [Category.assoc, RelativeRoot.finiteProductPointsEquiv_symm_π, splitInv,
      RelativeRoot.finiteProductPointsEquiv_symm_π, Fin.addCases_left]
  · rw [Category.assoc, splitHom, lift_snd, Category.id_comp]
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, splitInv, RelativeRoot.finiteProductPointsEquiv_symm_π,
        Fin.addCases_right, Fin.cases_zero]
    · rw [Category.assoc, lift_snd]
      apply Fan.IsLimit.hom_ext (RelativeRoot.finiteProductIsLimit (posFactor H))
      intro r
      change (splitInv H ≫ _) ≫ (Pi.π (posFactor H) r).hom.hom =
        (snd _ _ ≫ snd _ _) ≫ (Pi.π (posFactor H) r).hom.hom
      rw [Category.assoc, RelativeRoot.finiteProductPointsEquiv_symm_π, splitInv,
        RelativeRoot.finiteProductPointsEquiv_symm_π, Fin.addCases_right, Fin.cases_succ,
        Category.assoc]

instance isIso_splitHom : IsIso (splitHom H) :=
  ⟨⟨splitInv H, splitHom_splitInv, splitInv_splitHom⟩⟩

/-- The ordered multiplication factors through the three-block cell multiplication. -/
theorem orderedMultiplication_eq_split (j : ∀ i, H i ⟶ G)
    {M Z U : GroupScheme B} (jM : M ⟶ G) (jZ : Z ⟶ G) (jU : U ⟶ G)
    (mN : (∏ᶜ negFactor H).X ⟶ M.X)
    (hmN : mN ≫ jM.hom.hom =
      RelativeRoot.orderedMultiplication (fun r => j (Fin.castAdd (n₂ + 1) r)))
    (t : (H (Fin.natAdd n₁ 0)).X ⟶ Z.X)
    (ht : t ≫ jZ.hom.hom = (j (Fin.natAdd n₁ 0)).hom.hom)
    (mP : (∏ᶜ posFactor H).X ⟶ U.X)
    (hmP : mP ≫ jU.hom.hom =
      RelativeRoot.orderedMultiplication (fun r => j (Fin.natAdd n₁ r.succ))) :
    RelativeRoot.orderedMultiplication j =
      splitHom H ≫ (mN ⊗ₘ (t ⊗ₘ mP)) ≫ Dynamic.tripleCellMultiplication jM jZ jU := by
  rw [splitHom, lift_map_assoc, lift_map, Dynamic.lift_tripleCellMultiplication]
  simp only [Category.assoc, hmN, ht, hmP,
    RelativeRoot.finiteProductPointsEquiv_symm_orderedMultiplication]
  conv_lhs => rw [← Category.id_comp (RelativeRoot.orderedMultiplication j),
    RelativeRoot.comp_orderedMultiplication]
  simp only [RelativeRoot.orderedPoints, RelativeRoot.finiteProductPointsEquiv_apply,
    Category.id_comp]
  rw [List.ofFn_add, List.prod_append, List.ofFn_succ, List.prod_cons]
  rfl

/-- **Three-block open cells.** If the negative and positive block products are
isomorphisms onto representatives of the opposite and positive dynamic unipotent
subgroups and the middle factor is an open immersion into a representative of the
dynamic centralizer, the whole ordered multiplication is an open immersion. -/
theorem isOpenImmersion_orderedMultiplication_of_split [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (j : ∀ i, H i ⟶ G) (χ : (Gm B).toGrp ⟶ G)
    {M Z U : GroupScheme B} {jM : M ⟶ G} {jZ : Z ⟶ G} {jU : U ⟶ G}
    (hM : (Dynamic.unipotent (CommGroupScheme.groupHom (Gm.powerHom B (-1)) ≫ χ)).IsRepresentedBy
      jM)
    (hZ : (Dynamic.centralizer χ).IsRepresentedBy jZ)
    (hU : (Dynamic.unipotent χ).IsRepresentedBy jU)
    (mN : (∏ᶜ negFactor H).X ⟶ M.X) [IsIso mN]
    (hmN : mN ≫ jM.hom.hom =
      RelativeRoot.orderedMultiplication (fun r => j (Fin.castAdd (n₂ + 1) r)))
    (t : (H (Fin.natAdd n₁ 0)).X ⟶ Z.X) [IsOpenImmersion t.left]
    (ht : t ≫ jZ.hom.hom = (j (Fin.natAdd n₁ 0)).hom.hom)
    (mP : (∏ᶜ posFactor H).X ⟶ U.X) [IsIso mP]
    (hmP : mP ≫ jU.hom.hom =
      RelativeRoot.orderedMultiplication (fun r => j (Fin.natAdd n₁ r.succ))) :
    IsOpenImmersion (RelativeRoot.orderedMultiplication j).left := by
  rw [orderedMultiplication_eq_split j jM jZ jU mN hmN t ht mP hmP]
  have hT := Dynamic.isOpenImmersion_tripleCellMultiplication_overBase χ hM hZ hU
  have : IsIso (splitHom H).left := (inferInstance : IsIso ((Over.forget B).map (splitHom H)))
  have : IsIso mN.left := (inferInstance : IsIso ((Over.forget B).map mN))
  have : IsIso mP.left := (inferInstance : IsIso ((Over.forget B).map mP))
  have : IsOpenImmersion (t ⊗ₘ mP).left := by
    rw [Over.tensorHom_left]
    infer_instance
  have : IsOpenImmersion (mN ⊗ₘ (t ⊗ₘ mP)).left := by
    rw [Over.tensorHom_left]
    infer_instance
  simp only [Over.comp_left]
  infer_instance

end Split

/-! ### The ordered integral open cell of the actual family -/

section Assembly

local instance {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : IsDiscreteValuationRing (fixedFieldIntegers F) :=
  fixedFieldIntegersIsDVR_of_valuesFromBase F (fixedFieldValuesFromBase F)

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
  [IsAffineHom G.X.hom]
  {C : MaximalUnramified.BuildingData F G} {E : UnramifiedZeroDatum F G}
  {Ω : Set C.Apartment}
  {N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G}
  [Smooth N.group.X.hom]
  (hpts : N.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω))
  (T : IntegralSplitTorusData N C.i)

omit [Smooth N.group.X.hom] in
include hpts in
/-- Ordered products of actual root points which are integral have integral
factors, for an injective enumeration of the indivisible roots positive on a
generic cocharacter. -/
theorem mem_integralPoints_of_orderedProduct (ϖ : cocharacterLattice C.S)
    (hϖ : IsGenericCocharacter C.i ϖ) {n : ℕ} (a : Fin n → relativeRoots C.i)
    (ha : Function.Injective a)
    (hrange : Set.range (fun r => (a r : characterLattice C.S)) =
      RelativeRoot.indivisiblePositiveRoots C.i ϖ)
    (u : Fin n → rationalPoints G)
    (hu : ∀ r, u r ∈ (RelativeRoot.subgroup C.i (a r)).carrier (Over.mk (𝟙 _)))
    (hprod : (List.ofFn u).prod ∈ N.integralPoints) (r : Fin n) :
    u r ∈ N.integralPoints := by
  have : Mono C.i.hom.hom.left := mono_of_isMaximalSplitTorus C.isMaximalSplitTorus
  rw [hpts] at hprod ⊢
  have hfix := (Subgroup.mem_inf.mp hprod).2
  have hmem : u r ∈ rootGroupPoints C.i (a r) ⊓ C.pointwiseFixer (C.apartmentMap '' Ω) := by
    refine ⟨hu r, ?_⟩
    change u r ∈ C.apartment.pointwiseFixer _
    rw [KPApartmentData.mem_pointwiseFixer]
    rintro _ ⟨y, hy, rfl⟩
    have hy' := (C.apartment.mem_pointwiseFixer.mp hfix) _ ⟨y, hy, rfl⟩
    have hf := C.apartment.mem_filtration_of_orderedProduct_smul_apartmentMap_eq
      C.isConnectedReductive C.isMaximalSplitTorus y ϖ hϖ (fun r => (a r : characterLattice C.S))
      (Subtype.val_injective.comp ha) hrange u hu hy' r
    exact C.apartment.mem_reducedFixer.mp
      ((C.apartment.sharpFixer_le_reducedFixer y)
        ((C.apartment.filtration_le_sharpFixer y (a r).2) hf))
  rw [C.apartment.rootGroupPoints_inf_pointwiseFixer_eq_rootFixer C.isConnectedReductive
    C.isMaximalSplitTorus (a r) Ω,
    ← rootGroupPoints_inf_unramifiedZeroFixer_eq_rootFixer C E Ω (a r)] at hmem
  exact hmem.2

/-- Unique ordered decompositions in the generic dynamic unipotent subgroup. -/
theorem existsUnique_orderedDecomposition (ϖ : cocharacterLattice C.S) {n : ℕ}
    (a : Fin n → relativeRoots C.i) (ha : Function.Injective a)
    (hrange : Set.range (fun r => (a r : characterLattice C.S)) =
      RelativeRoot.indivisiblePositiveRoots C.i ϖ)
    (T' : Over (Spec (CommRingCat.of (inertiaFixedField F)))) (g : T' ⟶ G.X)
    (hg : g ∈ (Dynamic.unipotent (CommGroupScheme.groupHom ϖ ≫ C.i)).carrier T') :
    ∃! x : ∀ r, (RelativeRoot.subgroup C.i (a r)).carrier T',
      (List.ofFn fun r => (x r : T' ⟶ G.X)).prod = g := by
  obtain ⟨U'', jU'', H'', j'', e, hU'', -, -, -, -, -, hH'', he⟩ :=
    RelativeRoot.dynamicRootOrderedProduct _ G C.isConnectedReductive C.S C.i
      C.isMaximalSplitTorus ϖ n (fun r => (a r : characterLattice C.S))
      (Subtype.val_injective.comp ha) hrange
  have hpos (r : Fin n) : 0 < latticePairing C.S (a r) ϖ :=
    (show (a r : characterLattice C.S) ∈ RelativeRoot.indivisiblePositiveRoots C.i ϖ from
      hrange ▸ Set.mem_range_self r).2
  have hjV (r : Fin n) : SubgroupFunctor.range (j'' r) ≤
      Dynamic.unipotent (CommGroupScheme.groupHom ϖ ≫ C.i) := by
    rw [(hH'' r).1.2]
    exact RelativeRoot.subgroup_le_dynamicUnipotent C.i ϖ (hpos r)
  have hiso := RelativeRoot.isIso_orderedMultiplication_factorHom_of_iso hU'' j'' hjV e he
  exact (RelativeRoot.isIso_orderedMultiplication_factorHom_iff hU'' j''
    (fun r => (hH'' r).1) hjV).mp hiso T' g hg

/-- The actual root model maps lie in the dynamic unipotent subgroup of a cocharacter
positive on the root, have generic fibre representing the actual root subgroup, and
lift every integral root point. -/
theorem rootModelMap_facts (a : relativeRoots C.i) (ϖ : cocharacterLattice C.S)
    (hpos : 0 < latticePairing C.S a ϖ) :
    SubgroupFunctor.range (T.rootModelMap a a.2.1).hom ≤
        Dynamic.unipotent (integralCocharacterHom T ϖ) ∧
      (RelativeRoot.subgroup C.i a).IsRepresentedBy
        (N.genericHom (T.rootModelMap a a.2.1).hom) ∧
      ∀ g ∈ N.integralPoints, g ∈ (RelativeRoot.subgroup C.i a).carrier (Over.mk (𝟙 _)) →
        ∃ s : rationalPoints (T.rootModel a a.2.1).group,
          N.integralPointMap (s ≫ (T.rootModelMap a a.2.1).hom.hom.hom) = g := by
  refine ⟨?_, T.rootInclusion_isRootSubgroup a a.2.1, ?_⟩
  · change SubgroupFunctor.range (IntegralModel.SplitRoot.integralHom N T.isSplit T.inclusion
      (T.integralCharacter a) (T.integralCharacter_ne_zero a.2.1)) ≤ _
    rw [(IntegralModel.SplitRoot.integral_properties N T.isSplit T.inclusion
      (T.integralCharacter a) (T.integralCharacter_ne_zero a.2.1)).1.2]
    apply RelativeRoot.subgroup_le_dynamicUnipotent_of_isDomain
    rw [latticePairing_integralCharacter_integralCocharacter]
    exact hpos
  · intro g hg hga
    have hmem : g ∈ (T.rootModel a a.2.1).integralPoints.map
        (rationalPoints.map (T.rootInclusion a a.2.1)) := by
      rw [T.rootModel_integralPoints_eq a a.2.1]
      exact ⟨hg, hga⟩
    obtain ⟨w, ⟨s, rfl⟩, rfl⟩ := hmem
    exact ⟨s, (T.rootModelMap a a.2.1).integralPointMap_naturality s⟩

/-- The relative identity component of the integral centralizer maps by an open
immersion into every representative of the dynamic centralizer of a generic
integral cocharacter. -/
theorem exists_isOpenImmersion_centralizer_factor (hrep : (torusCentralizer C.i).IsRepresentedBy E.i)
    (ϖ : cocharacterLattice C.S) (hϖ : IsGenericCocharacter C.i ϖ)
    {H : GroupScheme (Spec (CommRingCat.of (fixedFieldIntegers F)))}
    {iH : H ⟶ (T.centralizerModel E.i hrep).group}
    (hiH : IsRelativeIdentityComponent _ iH)
    {Z : GroupScheme (Spec (CommRingCat.of (fixedFieldIntegers F)))} {jZ : Z ⟶ N.group}
    [IsClosedImmersion jZ.hom.hom.left] [Flat Z.X.hom]
    (hZ : (Dynamic.centralizer (integralCocharacterHom T ϖ)).IsRepresentedBy jZ) :
    ∃ h : SubgroupFunctor.range (iH ≫ T.centralizerIntegralInclusion) ≤
        Dynamic.centralizer (integralCocharacterHom T ϖ),
      IsOpenImmersion (hZ.factorHom _ h).hom.hom.left := by
  have : Smooth G.X.hom := C.isConnectedReductive.smooth
  have : ConnectedSpace G.X.left := C.isConnectedReductive.connectedSpace
  have hc : SubgroupFunctor.range T.centralizerIntegralInclusion ≤
      Dynamic.centralizer (integralCocharacterHom T ϖ) := by
    rw [T.centralizer_properties.2.2.2]
    exact torusCentralizer_le_dynamicCentralizer T.inclusion _
  have h : SubgroupFunctor.range (iH ≫ T.centralizerIntegralInclusion) ≤
      Dynamic.centralizer (integralCocharacterHom T ϖ) :=
    (SubgroupFunctor.range_comp_le _ _).trans hc
  refine ⟨h, ?_⟩
  have hfac : hZ.factorHom (iH ≫ T.centralizerIntegralInclusion) h =
      iH ≫ hZ.factorHom T.centralizerIntegralInclusion hc :=
    (SubgroupFunctor.IsRepresentedBy.factorHom_unique hZ _ h
      (by rw [Category.assoc, SubgroupFunctor.IsRepresentedBy.factorHom_comp])).symm
  have : IsClosedImmersion T.centralizerIntegralInclusion.hom.hom.left :=
    T.centralizer_properties.1
  have hK₂ : (torusCentralizer C.i).IsRepresentedBy (N.genericHom jZ) := by
    rw [← IsSplitTorus.dynamicCentralizer_eq_torusCentralizer
      C.isMaximalSplitTorus.isSplitSubtorus.1 C.i ϖ hϖ]
    exact isRepresentedBy_genericHom_centralizer T ϖ hZ
  have hiso : IsIso (hZ.factorHom T.centralizerIntegralInclusion hc).hom.hom :=
    isIso_factorHom_of_generic N T.centralizerIntegralInclusion jZ hZ hc
      T.centralizer_generic_isRepresentedBy hK₂
  rw [hfac]
  have : IsOpenImmersion iH.hom.hom.left := hiH.isOpenImmersion
  have : IsIso (hZ.factorHom T.centralizerIntegralInclusion hc).hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).map
      (hZ.factorHom T.centralizerIntegralInclusion hc).hom.hom))
  change IsOpenImmersion (iH.hom.hom.left ≫
    (hZ.factorHom T.centralizerIntegralInclusion hc).hom.hom.left)
  infer_instance

set_option maxHeartbeats 1600000 in
/-- **The ordered integral open cell of the actual family.** For a generic
cocharacter and injective enumerations of the indivisible roots of both signs, the
ordered multiplication of the actual family is an open immersion. -/
theorem isOpenImmersion_family (hrep : (torusCentralizer C.i).IsRepresentedBy E.i)
    [GeometricallyConnected E.T.toGrp.X.hom]
    (hne : Ω.Nonempty) (hb : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω)) (x : C.Apartment)
    {H : GroupScheme (Spec (CommRingCat.of (fixedFieldIntegers F)))}
    {iH : H ⟶ (T.centralizerModel E.i hrep).group}
    (hiH : IsRelativeIdentityComponent _ iH) (hH : Smooth H.X.hom)
    (hgc : GeometricallyConnected H.X.hom)
    (htor : ((T.centralizerModel E.i hrep).neutralModel
      (T.centralizerModel_isSmooth E.i hrep) hiH hH).integralPoints = E.torusIwahori)
    (ν : cocharacterLattice C.S) (hν : IsGenericCocharacter C.i ν)
    {nneg npos : ℕ} (aneg : Fin nneg → relativeRoots C.i)
    (apos : Fin npos → relativeRoots C.i)
    (hinjN : Function.Injective aneg)
    (hrN : Set.range (fun j => (aneg j : characterLattice C.S)) =
      RelativeRoot.indivisiblePositiveRoots C.i (-ν))
    (hinjP : Function.Injective apos)
    (hrP : Set.range (fun j => (apos j : characterLattice C.S)) =
      RelativeRoot.indivisiblePositiveRoots C.i ν) :
    IsOpenImmersion ((family hrep hpts hne hb T x hiH hH hgc htor).orderedIntegralMultiplication
      aneg apos).left := by
  obtain ⟨hdvr, hhens, hsep⟩ := fixedFieldIntegers_strictHenselian F
  set A := family hrep hpts hne hb T x hiH hH hgc htor with hA
  have hνn : IsGenericCocharacter C.i (-ν) := by
    intro a ha
    simpa only [map_neg] using neg_ne_zero.mpr (hν a ha)
  have : IsAffine N.group.X.left := isAffine_of_isAffineHom N.group.X.hom
  obtain ⟨M, jM, hMcl, -, hM⟩ :=
    (dynamicBaseRepresentability _ N.group (integralCocharacterHom T (-ν))).2.1
  obtain ⟨Z, jZ, hZcl, -, hZ⟩ :=
    (dynamicBaseRepresentability _ N.group (integralCocharacterHom T ν)).2.2
  obtain ⟨U, jU, hUcl, -, hU⟩ :=
    (dynamicBaseRepresentability _ N.group (integralCocharacterHom T ν)).2.1
  have : Smooth M.X.hom := (DynamicBaseOppositeCell.smooth_representatives _ M jM).2 hM
  have : Smooth U.X.hom := (DynamicBaseOppositeCell.smooth_representatives _ U jU).2 hU
  have : Smooth Z.X.hom :=
    Dynamic.smooth_centralizer_overRing _ inferInstance jZ hZ
  have : IsClosedImmersion jZ.hom.hom.left := hZcl
  have : IsAffineHom M.X.hom := by
    have : IsClosedImmersion jM.hom.hom.left := hMcl
    rw [← jM.hom.hom.w]
    infer_instance
  have : IsAffineHom U.X.hom := by
    have : IsClosedImmersion jU.hom.hom.left := hUcl
    rw [← jU.hom.hom.w]
    infer_instance
  have hidxN (r : Fin nneg) : TorusRootModelFamilyData.orderedIntegralIndex aneg apos
      (Fin.castAdd (npos + 1) r) = some (aneg r) := by
    simp [TorusRootModelFamilyData.orderedIntegralIndex]
  have hidx0 : TorusRootModelFamilyData.orderedIntegralIndex aneg apos
      (Fin.natAdd nneg 0) = none := by
    simp [TorusRootModelFamilyData.orderedIntegralIndex]
  have hidxP (r : Fin npos) : TorusRootModelFamilyData.orderedIntegralIndex aneg apos
      (Fin.natAdd nneg r.succ) = some (apos r) := by
    simp [TorusRootModelFamilyData.orderedIntegralIndex]
  have hfacts : ∀ (i : Option (relativeRoots C.i)) (a : relativeRoots C.i)
      (ϖ : cocharacterLattice C.S), i = some a → 0 < latticePairing C.S a ϖ →
      SubgroupFunctor.range (A.modelMap i).hom ≤
          Dynamic.unipotent (integralCocharacterHom T ϖ) ∧
        (RelativeRoot.subgroup C.i a).IsRepresentedBy (N.genericHom (A.modelMap i).hom) ∧
        ∀ g ∈ N.integralPoints, g ∈ (RelativeRoot.subgroup C.i a).carrier (Over.mk (𝟙 _)) →
          ∃ s : rationalPoints (A.model i).group,
            N.integralPointMap (s ≫ (A.modelMap i).hom.hom.hom) = g := by
    rintro i a ϖ rfl hpos
    exact rootModelMap_facts T a ϖ hpos
  have hposN (r : Fin nneg) : 0 < latticePairing C.S (aneg r) (-ν) :=
    (show (aneg r : characterLattice C.S) ∈ RelativeRoot.indivisiblePositiveRoots C.i (-ν) from
      hrN ▸ Set.mem_range_self r).2
  have hposP (r : Fin npos) : 0 < latticePairing C.S (apos r) ν :=
    (show (apos r : characterLattice C.S) ∈ RelativeRoot.indivisiblePositiveRoots C.i ν from
      hrP ▸ Set.mem_range_self r).2
  have hsmooth (i : Fin (nneg + (npos + 1))) :
      Smooth (A.orderedIntegralFactor aneg apos i).X.hom := A.smooth _
  have haff (i : Fin (nneg + (npos + 1))) :
      IsAffineHom (A.orderedIntegralFactor aneg apos i).X.hom :=
    (A.model (TorusRootModelFamilyData.orderedIntegralIndex aneg apos i)).affine
  let fN : ∀ r : Fin nneg, A.orderedIntegralFactor aneg apos (Fin.castAdd (npos + 1) r) ⟶
      N.group := fun r => A.orderedIntegralFactorMap aneg apos (Fin.castAdd (npos + 1) r)
  let fP : ∀ r : Fin npos, A.orderedIntegralFactor aneg apos (Fin.natAdd nneg r.succ) ⟶
      N.group := fun r => A.orderedIntegralFactorMap aneg apos (Fin.natAdd nneg r.succ)
  have hfN (r : Fin nneg) := hfacts _ (aneg r) (-ν) (hidxN r) (hposN r)
  have hfP (r : Fin npos) := hfacts _ (apos r) ν (hidxP r) (hposP r)
  have hisoN : IsIso (RelativeRoot.orderedMultiplication
      (fun r => hM.factorHom (fN r) (hfN r).1)) :=
    isIso_orderedMultiplication_of_generic N (hHs := fun r => hsmooth _)
      (hHa := fun r => haff _) fN hM (fun r => (hfN r).1)
      (FK := fun r => RelativeRoot.subgroup C.i (aneg r)) (fun r => (hfN r).2.1)
      (isRepresentedBy_genericHom_unipotent T (-ν) hM)
      (existsUnique_orderedDecomposition (-ν) aneg hinjN hrN)
      (fun u hu hprod r => mem_integralPoints_of_orderedProduct hpts (-ν) hνn aneg hinjN hrN
        u hu hprod r)
      (fun r g hg hga => (hfN r).2.2 g hg hga)
  have hisoP : IsIso (RelativeRoot.orderedMultiplication
      (fun r => hU.factorHom (fP r) (hfP r).1)) :=
    isIso_orderedMultiplication_of_generic N (hHs := fun r => hsmooth _)
      (hHa := fun r => haff _) fP hU (fun r => (hfP r).1)
      (FK := fun r => RelativeRoot.subgroup C.i (apos r)) (fun r => (hfP r).2.1)
      (isRepresentedBy_genericHom_unipotent T ν hU)
      (existsUnique_orderedDecomposition ν apos hinjP hrP)
      (fun u hu hprod r => mem_integralPoints_of_orderedProduct hpts ν hν apos hinjP hrP
        u hu hprod r)
      (fun r g hg hga => (hfP r).2.2 g hg hga)
  obtain ⟨htle, hopen⟩ := exists_isOpenImmersion_centralizer_factor T hrep ν hν hiH hZ
  have htorus : ∀ i : Option (relativeRoots C.i), i = none →
      ∃ h : SubgroupFunctor.range (A.modelMap i).hom ≤
          Dynamic.centralizer (integralCocharacterHom T ν),
        IsOpenImmersion (hZ.factorHom _ h).hom.hom.left := by
    rintro i rfl
    exact ⟨htle, hopen⟩
  obtain ⟨h0, hopen0⟩ := htorus _ hidx0
  have hMtriple : (Dynamic.unipotent (CommGroupScheme.groupHom
      (Gm.powerHom (Spec (CommRingCat.of (fixedFieldIntegers F))) (-1)) ≫
        integralCocharacterHom T ν)).IsRepresentedBy jM := by
    have h := hM
    rw [integralCocharacterHom_neg] at h
    exact h
  show IsOpenImmersion (RelativeRoot.orderedMultiplication
    (A.orderedIntegralFactorMap aneg apos)).left
  exact isOpenImmersion_orderedMultiplication_of_split (A.orderedIntegralFactorMap aneg apos)
    (integralCocharacterHom T ν) hMtriple hZ hU
    (RelativeRoot.orderedMultiplication (fun r => hM.factorHom (fN r) (hfN r).1))
    (RelativeRoot.orderedMultiplication_factorHom hM fN (fun r => (hfN r).1))
    (hZ.factorHom _ h0).hom.hom
    (by rw [← Grp.comp_hom_hom, SubgroupFunctor.IsRepresentedBy.factorHom_comp]; rfl)
    (RelativeRoot.orderedMultiplication (fun r => hU.factorHom (fP r) (hfP r).1))
    (RelativeRoot.orderedMultiplication_factorHom hU fP (fun r => (hfP r).1))

end Assembly

end OrderedIntegralOpenCell

end Langlands.BruhatTits.IntegralModels
