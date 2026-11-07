import Langlands.GroupScheme.Reductive.LocalSplitCell
import Langlands.GroupScheme.Rational.DynamicRootProductRayReduction
import Langlands.GroupScheme.Rational.OrderedProductPoints
import Langlands.GroupScheme.Rational.SteinbergRootMapUniqueness
import Langlands.GroupScheme.Rational.GenericCentralizerProof
import Langlands.GroupScheme.Rational.RelativeTitsNondegeneracy
import Langlands.GroupScheme.Absolute.OppositeCellProof
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof
import Langlands.GroupScheme.Torus.MaximalSplitComparison
import Langlands.GroupScheme.Dynamic.LimitMap

/-! # The big cell of a split reductive group over a field -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitBigCell

open RelativeRoot LocalSplitCell

/-! ### Points of root parametrizations and of ordered products -/

section Points

variable {R : Type u} [CommRing R] {G : GroupScheme (Spec (CommRingCat.of R))}

/-- A map `𝔾ₐ ⟶ G` representing a subgroup functor is injective on points. -/
theorem rootPoint_injective {F : SubgroupFunctor G} {u : Ga R ⟶ G} (hu : F.IsRepresentedBy u)
    (Z : Over (Spec (CommRingCat.of R))) : Function.Injective (rootPoint u Z) := by
  intro c c' h
  have : Mono u.hom.hom := hu.1
  unfold rootPoint at h
  have h' := (cancel_mono u.hom.hom).1 h
  simpa only [VectorGroup.coordinates_scalarPoint] using
    congrArg (fun x => (VectorGroup.coordinates (CommRingCat.of R) 1 Z x).toAdd 0) h'

/-- The points of a subgroup functor represented by `u : 𝔾ₐ ⟶ G` are the values of `u`. -/
theorem mem_iff_exists_rootPoint {F : SubgroupFunctor G} {u : Ga R ⟶ G}
    (hu : F.IsRepresentedBy u) {Z : Over (Spec (CommRingCat.of R))} (g : Z ⟶ G.X) :
    g ∈ F.carrier Z ↔ ∃ c, rootPoint u Z c = g := by
  rw [← hu.2, SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨(VectorGroup.coordinates (CommRingCat.of R) 1 Z y).toAdd 0, by
      rw [rootPoint, VectorGroup.scalarPoint_coordinate]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨_, rfl⟩

/-- If the ordered multiplication of groups `H r` representing subgroup functors `F r` is
an isomorphism onto a group representing `F`, and `u (pos r)` also represents `F r`, then on
every test scheme the ordered product of the values of `u` is injective with image the points
of `F`. -/
theorem orderedProduct_points_of_iso {J : Type u} {F : SubgroupFunctor G}
    {U : GroupScheme (Spec (CommRingCat.of R))} {jU : U ⟶ G} (hjU : F.IsRepresentedBy jU)
    {n : ℕ} {H : Fin n → GroupScheme (Spec (CommRingCat.of R))} (j : ∀ r, H r ⟶ G)
    (e : (∏ᶜ H).X ≅ U.X) (he : e.hom ≫ jU.hom.hom = orderedMultiplication j)
    (Fr : Fin n → SubgroupFunctor G) (hj : ∀ r, (Fr r).IsRepresentedBy (j r))
    (u : J → (Ga R ⟶ G)) (pos : Fin n → J) (hu : ∀ r, (Fr r).IsRepresentedBy (u (pos r)))
    (Z : Over (Spec (CommRingCat.of R))) :
    Function.Injective (orderedProduct u pos Z) ∧
      ∀ g : Z ⟶ G.X, g ∈ F.carrier Z ↔ ∃ w, orderedProduct u pos Z w = g := by
  let x : (Fin n → Γ(Z.left, ⊤)) → (Z ⟶ (∏ᶜ H).X) := fun w =>
    (finiteProductPointsEquiv H Z).symm fun r => ((hj r).pointsEquiv Z).symm
      ⟨rootPoint (u (pos r)) Z (w r), (mem_iff_exists_rootPoint (hu r) _).2 ⟨_, rfl⟩⟩
  have hx (w : Fin n → Γ(Z.left, ⊤)) :
      x w ≫ e.hom ≫ jU.hom.hom = orderedProduct u pos Z w := by
    rw [he, finiteProductPointsEquiv_symm_orderedMultiplication]
    simp only [orderedPoints, orderedProduct,
      SubgroupFunctor.IsRepresentedBy.pointsEquiv_symm_comp]
  refine ⟨fun w w' h => ?_, fun g => ⟨fun hg => ?_, ?_⟩⟩
  · have : Mono jU.hom.hom := hjU.1
    rw [← hx, ← hx] at h
    have h1 := (finiteProductPointsEquiv H Z).symm.injective ((cancel_mono _).1 h)
    funext r
    have h2 := congrArg Subtype.val (((hj r).pointsEquiv Z).symm.injective (congrFun h1 r))
    exact rootPoint_injective (hu r) Z h2
  · rw [← hjU.2, SubgroupFunctor.mem_range] at hg
    obtain ⟨y, rfl⟩ := hg
    have hp (r : Fin n) :
        finiteProductPointsEquiv H Z (y ≫ e.inv) r ≫ (j r).hom.hom ∈ (Fr r).carrier Z := by
      rw [← (hj r).2]
      exact SubgroupFunctor.mem_range.2 ⟨_, rfl⟩
    choose w hw using fun r => (mem_iff_exists_rootPoint (hu r) _).1 (hp r)
    refine ⟨w, ?_⟩
    have h1 : orderedProduct u pos Z w = orderedPoints j (finiteProductPointsEquiv H Z (y ≫ e.inv)) := by
      simp only [orderedProduct, orderedPoints, hw]
    rw [h1, ← finiteProductPointsEquiv_symm_orderedMultiplication, MulEquiv.symm_apply_apply, ← he]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  · rintro ⟨w, rfl⟩
    rw [← hx, ← hjU.2]
    exact SubgroupFunctor.mem_range.2 ⟨x w ≫ e.hom, Category.assoc _ _ _⟩

end Points

variable {k : Type u} [Field k]

/-! ### Ordered products of root groups -/

/-- The ordered product over the indivisible positive roots of a single group, assuming only the
ray data of that group and cocharacter. This repeats the proof of
`dynamicRootOrderedProduct_of_splitUnipotentSourceProducts` with the ray decomposition supplied
for one group. -/
theorem exists_orderedProduct_of_rays
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (i : S.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice S)
    (hdisj : letI := hG.isAffineHom
      ∀ a ∈ indivisiblePositiveRoots i ν, ∀ b ∈ indivisiblePositiveRoots i ν, a ≠ b →
        Disjoint (cyclicTail a 1 : Set (characterLattice S))
          (cyclicTail b 1 : Set (characterLattice S)))
    (hcover : letI := hG.isAffineHom
      ∀ χ ∈ relativeRoots i,
        0 < latticePairing S χ ν ↔ ∃ a ∈ indivisiblePositiveRoots i ν, χ ∈ cyclicTail a 1)
    (n : ℕ) (a : Fin n → characterLattice S) (hinj : Function.Injective a)
    (ha : letI := hG.isAffineHom; Set.range a = indivisiblePositiveRoots i ν) :
    letI := hG.isAffineHom
    ∃ (U : GroupScheme (Spec (CommRingCat.of k))) (jU : U ⟶ G)
      (H : Fin n → GroupScheme (Spec (CommRingCat.of k))) (j : ∀ r, H r ⟶ G)
      (e : (∏ᶜ H).X ≅ U.X),
      (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy jU ∧
      (∀ r, (subgroup i (a r)).IsRepresentedBy (j r)) ∧
      e.hom ≫ jU.hom.hom = orderedMultiplication j := by
  let := hG.isAffineHom
  let b := AutomorphicAction.conjugation i
  let A := positiveSemigroup ν
  obtain ⟨⟨U, jU, hjU, hjUc, hUs, hUc⟩, hStable, _, hUnip, _, _⟩ :=
    semigroupRealization k G hG.smooth inferInstance S hi.1.1 b A
  have hzero : (0 : characterLattice S) ∉ A := by
    change ¬ 0 < latticePairing S 0 ν
    simp
  obtain ⟨hUu, _⟩ := hUnip U jU hjU hzero
  let : IsAffineHom U.X.hom := hjUc.isAffineHom
  let c := b.onRepresentedSubgroup jU hjU hStable
  have hequiv : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X)
      (x : T ⟶ U.X), c.act s x ≫ jU.hom.hom = b.act s (x ≫ jU.hom.hom) :=
    fun _ s x => b.onRepresentedSubgroup_act_comp jU hjU hStable s x
  have htop : (⊤ : SubgroupFunctor U).map jU = semigroupSubgroup b A := by
    rw [SubgroupFunctor.map_top, hjU.2]
  have hsupport : actionWeightSupport c ⊤ = positiveRelativeRoots i ν := by
    rw [← actionWeightSupport_map jU hjU.1 c b hequiv, htop]
    exact actionWeightSupport_positiveSemigroup semigroupRealization hG.smooth hi.1.1 i ν
  have hblocks := rootRayBlock_pairwise i ν a hinj ha hdisj
  have hcover' : (⋃ r, rootRayBlock i (a r)) = actionWeightSupport c ⊤ :=
    (iUnion_rootRayBlock i ν a ha hcover).trans hsupport.symm
  let := hUs
  let := hUc
  obtain ⟨H, jH, hH, hIso⟩ := hasOrderedSemigroupProducts_of_unipotent c hi.1.1 hUu n
    (fun r => rootRayBlock i (a r)) hcover' hblocks.1 hblocks.2
  have hroot (r : Fin n) : a r ∈ indivisiblePositiveRoots i ν :=
    ha ▸ Set.mem_range_self r
  have hsemigroup (r : Fin n) :
      ((semigroupSubgroup c (AddSubsemigroup.closure (rootRayBlock i (a r)))).map jU) =
        semigroupSubgroup b (cyclicTail (a r) 1) := by
    rw [closure_rootRayBlock i (hroot r).1.1]
    apply semigroupSubgroup_map_eq jU hjUc c b hequiv
    rw [hjU.2]
    exact semigroupSubgroup_mono b (cyclicTail_one_le_positiveSemigroup (hroot r).2)
  have hfactor (r : Fin n) : (subgroup i (a r)).IsRepresentedBy (jH r ≫ jU) := by
    have hcyclic := cyclicRootFunctorComparison k G hG.smooth inferInstance S hi.1.1 i (a r)
      (hroot r).1.1.1
    have hrep : (semigroupSubgroup b (cyclicTail (a r) 1)).IsRepresentedBy (jH r ≫ jU) := by
      rw [← hsemigroup r]
      exact (hH r).1.comp hjU
    exact hcyclic ▸ hrep
  let := hIso
  refine ⟨U, jU, H, (fun r => jH r ≫ jU), asIso (orderedMultiplication jH), ?_, hfactor, ?_⟩
  · rw [(dynamicSemigroupComparison k G hG.smooth inferInstance hG.connectedSpace S hi.1.1
      i ν).2.2]
    exact hjU
  · exact orderedMultiplication_comp jH jU

/-- The relative roots of `i` have reduced rays: two positive multiples of roots agree only for
equal roots and equal multiples. -/
def ReducedRays {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))} (i : S.toGrp ⟶ G) : Prop :=
  ∀ β₁ ∈ relativeRoots i, ∀ β₂ ∈ relativeRoots i, ∀ p q : ℕ, 0 < p → 0 < q →
    p • β₁ = q • β₂ → β₁ = β₂ ∧ p = q

/-- With reduced rays, every positive root is indivisible. -/
theorem indivisiblePositiveRoots_eq {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] {S : CommGroupScheme (Spec (CommRingCat.of k))} {i : S.toGrp ⟶ G}
    (hred : ReducedRays i) (ν : cocharacterLattice S) :
    indivisiblePositiveRoots i ν = {β | β ∈ relativeRoots i ∧ 0 < latticePairing S β ν} := by
  ext β
  constructor
  · rintro ⟨⟨hβ, _⟩, hpos⟩
    exact ⟨hβ, hpos⟩
  · rintro ⟨hβ, hpos⟩
    refine ⟨⟨hβ, fun b hb m hm h => ?_⟩, hpos⟩
    have := (hred b hb β hβ m 1 (by omega) one_pos (by rw [h, one_nsmul])).2
    omega

/-- The ordered product over the positive roots, for a group whose roots have reduced rays. -/
theorem exists_orderedProduct_of_reducedRays
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (i : S.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice S)
    (hred : letI := hG.isAffineHom; ReducedRays i)
    (n : ℕ) (a : Fin n → characterLattice S) (hinj : Function.Injective a)
    (ha : letI := hG.isAffineHom;
      Set.range a = {β | β ∈ relativeRoots i ∧ 0 < latticePairing S β ν}) :
    letI := hG.isAffineHom
    ∃ (U : GroupScheme (Spec (CommRingCat.of k))) (jU : U ⟶ G)
      (H : Fin n → GroupScheme (Spec (CommRingCat.of k))) (j : ∀ r, H r ⟶ G)
      (e : (∏ᶜ H).X ≅ U.X),
      (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy jU ∧
      (∀ r, (subgroup i (a r)).IsRepresentedBy (j r)) ∧
      e.hom ≫ jU.hom.hom = orderedMultiplication j := by
  let := hG.isAffineHom
  have hind := indivisiblePositiveRoots_eq hred ν
  refine exists_orderedProduct_of_rays G hG S i hi ν ?_ ?_ n a hinj (ha.trans hind.symm)
  · intro b₁ hb₁ b₂ hb₂ hb
    rw [Set.disjoint_left]
    rintro x ⟨p, _, hp, rfl⟩ ⟨q, _, hq, h⟩
    exact hb (hred b₁ hb₁.1.1 b₂ hb₂.1.1 p q hp hq h.symm).1
  · intro χ hχ
    rw [hind]
    constructor
    · intro h
      exact ⟨χ, ⟨hχ, h⟩, 1, le_rfl, one_pos, one_nsmul χ⟩
    · rintro ⟨b, ⟨_, hb⟩, p, _, hp, rfl⟩
      rw [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
      exact mul_pos (by exact_mod_cast hp) hb

/-- On every test scheme, the ordered product of the values of root parametrizations of the
positive roots is injective, with image the points of `U(ν)`. -/
theorem orderedProduct_points
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (i : S.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice S)
    (hred : letI := hG.isAffineHom; ReducedRays i)
    {J : Type u} (u : J → (Ga k ⟶ G)) {n : ℕ} (pos : Fin n → J)
    (a : Fin n → characterLattice S) (hinj : Function.Injective a)
    (ha : letI := hG.isAffineHom;
      Set.range a = {β | β ∈ relativeRoots i ∧ 0 < latticePairing S β ν})
    (hu : ∀ r, (subgroup i (a r)).IsRepresentedBy (u (pos r)))
    (Z : Over (Spec (CommRingCat.of k))) :
    Function.Injective (orderedProduct u pos Z) ∧
      ∀ g : Z ⟶ G.X, g ∈ (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier Z ↔
        ∃ w, orderedProduct u pos Z w = g := by
  let := hG.isAffineHom
  obtain ⟨U, jU, H, j, e, hU, hj, he⟩ :=
    exists_orderedProduct_of_reducedRays G hG S i hi ν hred n a hinj ha
  exact orderedProduct_points_of_iso hU j e he _ hj u pos hu Z

/-! ### The Levi decomposition of a generic parabolic -/

/-- For a generic cocharacter `ν` of a maximal split torus, every point of `P(ν)` is uniquely
`i(t) x` with `x` a point of `U(ν)`. -/
theorem parabolic_points
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsSplitTorus S.toGrp)
    (i : S.toGrp ⟶ G) (hi : IsMaximalTorus i) (ν : cocharacterLattice S)
    (hgen : letI := hG.isAffineHom; IsGenericCocharacter i ν)
    (Z : Over (Spec (CommRingCat.of k))) :
    (∀ g : Z ⟶ G.X, g ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier Z ↔
      ∃ t : Z ⟶ S.X, ∃ x ∈ (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier Z,
        (t ≫ i.hom.hom) * x = g) ∧
    ∀ (t t' : Z ⟶ S.X) (x x' : Z ⟶ G.X),
      x ∈ (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier Z →
      x' ∈ (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier Z →
      (t ≫ i.hom.hom) * x = (t' ≫ i.hom.hom) * x' → t = t' ∧ x = x' := by
  let := hG.isAffineHom
  have hZ : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) = SubgroupFunctor.range i := by
    rw [genericCentralizer k G hG S i (hi.isMaximalSplitTorus hT) ν hgen,
      maximalTorusCentralizer k G hG S i hi]
  have hmem (t : Z ⟶ S.X) :
      t ≫ i.hom.hom ∈ (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).carrier Z := by
    rw [hZ]
    exact SubgroupFunctor.mem_range.2 ⟨t, rfl⟩
  have : Mono i.hom.hom := by
    let : IsClosedImmersion i.hom.hom.left := hi.2.1
    exact Over.mono_of_mono_left _
  refine ⟨fun g => ⟨fun hg => ?_, ?_⟩, fun t t' x x' hx hx' h => ?_⟩
  · obtain ⟨l, hl⟩ := Dynamic.exists_hasLimit _ hg
    have hlZ := Dynamic.HasLimit.mem_centralizer _ hl
    obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.1 (hZ ▸ hlZ)
    refine ⟨t, (t ≫ i.hom.hom)⁻¹ * g, ?_, mul_inv_cancel_left _ _⟩
    have h := Dynamic.HasLimit.mul _
      (Dynamic.HasLimit.inv _ (Dynamic.hasLimit_of_mem_centralizer _ hlZ)) hl
    rwa [inv_mul_cancel] at h
  · rintro ⟨t, x, hx, rfl⟩
    exact Subgroup.mul_mem _ (Dynamic.centralizer_le_parabolic _ Z (hmem t))
      (Dynamic.unipotent_le_parabolic _ Z hx)
  · have hzu : (t' ≫ i.hom.hom)⁻¹ * (t ≫ i.hom.hom) ∈
        (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).carrier Z :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (hmem t')) (hmem t)
    have heq : (t' ≫ i.hom.hom)⁻¹ * (t ≫ i.hom.hom) = x' * x⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_inv_cancel_right]
    have huu : (t' ≫ i.hom.hom)⁻¹ * (t ≫ i.hom.hom) ∈
        (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier Z := by
      rw [heq]
      exact Subgroup.mul_mem _ hx' (Subgroup.inv_mem _ hx)
    have h1 := Dynamic.eq_one_of_mem_centralizer_of_mem_unipotent _
      (fun _ _ _ _ hl hl' => Dynamic.HasLimit.unique _ hl hl') hzu huu
    have hti : t ≫ i.hom.hom = t' ≫ i.hom.hom := (inv_mul_eq_one.1 h1).symm
    refine ⟨(cancel_mono _).1 hti, ?_⟩
    rw [hti] at h
    exact mul_left_cancel h

/-! ### The big cell -/

/-- If the multiplication map `U × P ⟶ G` of two subgroups is an open immersion and the
points `a`, `b` of `U` and `P` over `C` induce bijections on points of every test scheme, then
the product `a · b : C ⟶ G` is an open immersion. -/
theorem isOpenImmersion_of_factorization {B : Scheme.{u}} {G U P : GroupScheme B}
    (iU : U ⟶ G) (iP : P ⟶ G)
    (hopen : IsOpenImmersion ((fst U.X P.X ≫ iU.hom.hom) * (snd U.X P.X ≫ iP.hom.hom)).left)
    {C : Over B} (a : C ⟶ U.X) (b : C ⟶ P.X)
    (hab : ∀ Z : Over B, Function.Bijective fun z : Z ⟶ C => (z ≫ a, z ≫ b)) :
    IsOpenImmersion ((a ≫ iU.hom.hom) * (b ≫ iP.hom.hom)).left := by
  have hfac : lift a b ≫ ((fst _ _ ≫ iU.hom.hom) * (snd _ _ ≫ iP.hom.hom)) =
      (a ≫ iU.hom.hom) * (b ≫ iP.hom.hom) := by
    rw [MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc]
  have : IsIso (lift a b) := by
    rw [isIso_iff_yoneda_map_bijective]
    intro Z
    have heq : (fun z : Z ⟶ C => z ≫ lift a b) =
        homEquivToProd.symm ∘ fun z : Z ⟶ C => (z ≫ a, z ≫ b) := by
      funext z
      simp only [Function.comp_apply, homEquivToProd_symm_apply, comp_lift]
    rw [heq]
    exact homEquivToProd.symm.bijective.comp (hab Z)
  rw [← hfac, Over.comp_left]
  have : IsIso (lift a b).left := inferInstanceAs (IsIso ((Over.forget _).map (lift a b)))
  infer_instance

/-- The points form of the factorization through the opposite cell: if `U(ν⁻¹)` and `P(ν)` are
represented by `iU` and `iP`, and the points `a`, `b` of `U(ν⁻¹)` and `P(ν)` over `C` are the
negative ordered product and the torus times the positive ordered product of coordinates
identifying the points of `C`, then `z ↦ (z a, z b)` is bijective on every test scheme. -/
theorem bijective_cellFactors
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsSplitTorus S.toGrp)
    (i : S.toGrp ⟶ G) (hi : IsMaximalTorus i) (ν : cocharacterLattice S)
    (hgen : letI := hG.isAffineHom; IsGenericCocharacter i ν)
    (hred : letI := hG.isAffineHom; ReducedRays i)
    {J : Type u} (u : J → (Ga k ⟶ G)) {m n : ℕ} (neg : Fin m → J) (pos : Fin n → J)
    (an : Fin m → characterLattice S) (hinjn : Function.Injective an)
    (han : letI := hG.isAffineHom;
      Set.range an = {β | β ∈ relativeRoots i ∧ latticePairing S β ν < 0})
    (hun : ∀ r, (subgroup i (an r)).IsRepresentedBy (u (neg r)))
    (ap : Fin n → characterLattice S) (hinjp : Function.Injective ap)
    (hap : letI := hG.isAffineHom;
      Set.range ap = {β | β ∈ relativeRoots i ∧ 0 < latticePairing S β ν})
    (hup : ∀ r, (subgroup i (ap r)).IsRepresentedBy (u (pos r)))
    {U P : GroupScheme (Spec (CommRingCat.of k))} (iU : U ⟶ G) (iP : P ⟶ G)
    (hU : (Dynamic.unipotent
      (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom ν ≫ i))).IsRepresentedBy iU)
    (hP : (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy iP)
    (C : Over (Spec (CommRingCat.of k))) (v₀ : Fin m → Γ(C.left, ⊤)) (t₀ : C ⟶ S.X)
    (w₀ : Fin n → Γ(C.left, ⊤))
    (hC : ∀ Z : Over (Spec (CommRingCat.of k)), Function.Bijective fun z : Z ⟶ C =>
      ((fun r => z.left.appTop (v₀ r)), z ≫ t₀, (fun r => z.left.appTop (w₀ r))))
    (a : C ⟶ U.X) (ha : a ≫ iU.hom.hom = orderedProduct u neg C v₀)
    (b : C ⟶ P.X) (hb : b ≫ iP.hom.hom = (t₀ ≫ i.hom.hom) * orderedProduct u pos C w₀)
    (Z : Over (Spec (CommRingCat.of k))) :
    Function.Bijective fun z : Z ⟶ C => (z ≫ a, z ≫ b) := by
  let := hG.isAffineHom
  have hi' := hi.isMaximalSplitTorus hT
  have han' : Set.range an = {β | β ∈ relativeRoots i ∧ 0 < latticePairing S β (-ν)} := by
    rw [han]
    ext β
    simp only [Set.mem_ofPred_eq, map_neg, neg_pos]
  have hneg :
      Function.Injective (orderedProduct u neg Z) ∧
        ∀ g : Z ⟶ G.X, g ∈ (Dynamic.unipotent
          (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom ν ≫ i))).carrier Z ↔
          ∃ w, orderedProduct u neg Z w = g := by
    have h := orderedProduct_points G hG S i hi' (-ν) hred u neg an hinjn han' hun Z
    rwa [groupHom_neg_comp_eq_oppositeCocharacter i ν] at h
  have hpos := orderedProduct_points G hG S i hi' ν hred u pos ap hinjp hap hup Z
  have hlevi := parabolic_points G hG S hT i hi ν hgen Z
  have : Mono iU.hom.hom := hU.1
  have : Mono iP.hom.hom := hP.1
  have hza (z : Z ⟶ C) :
      (z ≫ a) ≫ iU.hom.hom = orderedProduct u neg Z fun r => z.left.appTop (v₀ r) := by
    rw [Category.assoc, ha, comp_orderedProduct]
  have hzb (z : Z ⟶ C) : (z ≫ b) ≫ iP.hom.hom =
      ((z ≫ t₀) ≫ i.hom.hom) * orderedProduct u pos Z fun r => z.left.appTop (w₀ r) := by
    rw [Category.assoc, hb, MonObj.comp_mul, comp_orderedProduct, Category.assoc]
  refine ⟨fun z z' h => ?_, fun y => ?_⟩
  · obtain ⟨h1, h2⟩ := Prod.mk.inj h
    have h1' : orderedProduct u neg Z (fun r => z.left.appTop (v₀ r)) =
        orderedProduct u neg Z (fun r => z'.left.appTop (v₀ r)) := by
      rw [← hza, ← hza, h1]
    have h2' : ((z ≫ t₀) ≫ i.hom.hom) * orderedProduct u pos Z (fun r => z.left.appTop (w₀ r)) =
        ((z' ≫ t₀) ≫ i.hom.hom) * orderedProduct u pos Z (fun r => z'.left.appTop (w₀ r)) := by
      rw [← hzb, ← hzb, h2]
    obtain ⟨ht, hw⟩ := hlevi.2 (z ≫ t₀) (z' ≫ t₀)
      (orderedProduct u pos Z (fun r => z.left.appTop (w₀ r)))
      (orderedProduct u pos Z (fun r => z'.left.appTop (w₀ r)))
      ((hpos.2 _).2 ⟨_, rfl⟩) ((hpos.2 _).2 ⟨_, rfl⟩) h2'
    exact (hC Z).1 (Prod.ext (hneg.1 h1') (Prod.ext ht (hpos.1 hw)))
  · obtain ⟨v, hv⟩ := (hneg.2 (y.1 ≫ iU.hom.hom)).1 (by
      rw [← hU.2]
      exact SubgroupFunctor.mem_range.2 ⟨y.1, rfl⟩)
    obtain ⟨t, x, hx, htx⟩ := (hlevi.1 (y.2 ≫ iP.hom.hom)).1 (by
      rw [← hP.2]
      exact SubgroupFunctor.mem_range.2 ⟨y.2, rfl⟩)
    obtain ⟨w, rfl⟩ := (hpos.2 x).1 hx
    obtain ⟨z, hz⟩ := (hC Z).2 (v, t, w)
    simp only [Prod.mk.injEq] at hz
    obtain ⟨hzv, hzt, hzw⟩ := hz
    refine ⟨z, Prod.ext ?_ ?_⟩
    · apply (cancel_mono iU.hom.hom).1
      change (z ≫ a) ≫ iU.hom.hom = y.1 ≫ iU.hom.hom
      rw [hza, hzv, hv]
    · apply (cancel_mono iP.hom.hom).1
      change (z ≫ b) ≫ iP.hom.hom = y.2 ≫ iP.hom.hom
      rw [hzb, hzw, hzt, htx]

/-- **The big cell over a field, in terms of points.** Let `ν` be a generic cocharacter of a
maximal split torus `i` whose roots have reduced rays, and let `u` be root parametrizations
enumerated by `neg` over the roots with `⟨β, ν⟩ < 0` and by `pos` over those with
`⟨β, ν⟩ > 0`. If `C` carries coordinates `v₀`, `t₀`, `w₀` identifying its points with triples
`(v, t, w)`, then the big-cell map `C ⟶ G`, `(v, t, w) ↦ (∏ u_{neg r}(v r)) i(t) (∏ u_{pos r}(w r))`,
is an open immersion. -/
theorem isOpenImmersion_of_points
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsSplitTorus S.toGrp)
    (i : S.toGrp ⟶ G) (hi : IsMaximalTorus i) (ν : cocharacterLattice S)
    (hgen : letI := hG.isAffineHom; IsGenericCocharacter i ν)
    (hred : letI := hG.isAffineHom; ReducedRays i)
    {J : Type u} (u : J → (Ga k ⟶ G)) {m n : ℕ} (neg : Fin m → J) (pos : Fin n → J)
    (an : Fin m → characterLattice S) (hinjn : Function.Injective an)
    (han : letI := hG.isAffineHom;
      Set.range an = {β | β ∈ relativeRoots i ∧ latticePairing S β ν < 0})
    (hun : ∀ r, (subgroup i (an r)).IsRepresentedBy (u (neg r)))
    (ap : Fin n → characterLattice S) (hinjp : Function.Injective ap)
    (hap : letI := hG.isAffineHom;
      Set.range ap = {β | β ∈ relativeRoots i ∧ 0 < latticePairing S β ν})
    (hup : ∀ r, (subgroup i (ap r)).IsRepresentedBy (u (pos r)))
    (C : Over (Spec (CommRingCat.of k))) (v₀ : Fin m → Γ(C.left, ⊤)) (t₀ : C ⟶ S.X)
    (w₀ : Fin n → Γ(C.left, ⊤))
    (hC : ∀ Z : Over (Spec (CommRingCat.of k)), Function.Bijective fun z : Z ⟶ C =>
      ((fun r => z.left.appTop (v₀ r)), z ≫ t₀, (fun r => z.left.appTop (w₀ r)))) :
    IsOpenImmersion
      (orderedProduct u neg C v₀ * (t₀ ≫ i.hom.hom) * orderedProduct u pos C w₀).left := by
  let := hG.isAffineHom
  let := hG.smooth
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hU := Dynamic.Affine.isRepresentedBy_unipotentHom
    (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom ν ≫ i))
  have hP := Dynamic.Affine.isRepresentedBy_parabolicHom (CommGroupScheme.groupHom ν ≫ i)
  have hopen := oppositeCellStatement k G (CommGroupScheme.groupHom ν ≫ i) _ _ _ _ hU hP
  have hi' := hi.isMaximalSplitTorus hT
  have han' : Set.range an = {β | β ∈ relativeRoots i ∧ 0 < latticePairing S β (-ν)} := by
    rw [han]
    ext β
    simp only [Set.mem_ofPred_eq, map_neg, neg_pos]
  have hmn : orderedProduct u neg C v₀ ∈ (Dynamic.unipotent
      (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom ν ≫ i))).carrier C := by
    have h := ((orderedProduct_points G hG S i hi' (-ν) hred u neg an hinjn han' hun C).2 _).2
      ⟨v₀, rfl⟩
    rwa [groupHom_neg_comp_eq_oppositeCocharacter i ν] at h
  have hmp : (t₀ ≫ i.hom.hom) * orderedProduct u pos C w₀ ∈
      (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier C :=
    ((parabolic_points G hG S hT i hi ν hgen C).1 _).2 ⟨t₀, _,
      ((orderedProduct_points G hG S i hi' ν hred u pos ap hinjp hap hup C).2 _).2 ⟨w₀, rfl⟩, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, a ≫ (Dynamic.Affine.unipotentHom
      (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom ν ≫ i))).hom.hom =
        orderedProduct u neg C v₀ :=
    ⟨_, hU.pointsEquiv_symm_comp ⟨_, hmn⟩⟩
  obtain ⟨b, hb⟩ : ∃ b, b ≫ (Dynamic.Affine.parabolicHom (CommGroupScheme.groupHom ν ≫ i)).hom.hom =
      (t₀ ≫ i.hom.hom) * orderedProduct u pos C w₀ :=
    ⟨_, hP.pointsEquiv_symm_comp ⟨_, hmp⟩⟩
  have h := isOpenImmersion_of_factorization _ _ hopen a b
    (bijective_cellFactors G hG S hT i hi ν hgen hred u neg pos an hinjn han hun ap hinjp hap hup
      _ _ hU hP C v₀ t₀ w₀ hC a ha b hb)
  rwa [ha, hb, ← mul_assoc] at h

end Langlands.GroupScheme.SplitBigCell
