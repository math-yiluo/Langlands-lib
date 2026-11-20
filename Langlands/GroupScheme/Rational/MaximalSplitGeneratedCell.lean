import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.MatrixRepresentation.TorusEquivariantAdditive
import Langlands.GroupScheme.Rational.SteinbergRootProduct
import Langlands.GroupScheme.Reductive.SplitRankOneRootCellUniversal
import Langlands.GroupScheme.Rational.RootSubgroup
import Langlands.GroupScheme.Reductive.SplitLeviGluingRankOneGraphClosure
import Langlands.GroupScheme.Reductive.SplitLeviGluingRationalDensity
import Langlands.GroupScheme.Reductive.SplitLeviGluingGraphDynamicFactors

/-! # The generated cell of the split subgroup -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.GroupScheme.MaximalSplitSubgroup

open VectorGroup RootCell

section Lines

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {H : GroupScheme (Spec (CommRingCat.of k))}

theorem crd_scalarPoint {Z : Over (Spec (CommRingCat.of k))} (c : Γ(Z.left, ⊤)) :
    crd (scalarPoint (CommRingCat.of k) Z c) = c :=
  coordinates_scalarPoint _ Z c 0

theorem scalarPoint_eq_pt {Z : Over (Spec (CommRingCat.of k))} (c : Γ(Z.left, ⊤)) :
    scalarPoint (CommRingCat.of k) Z c = pt c :=
  crd_injective (by rw [crd_scalarPoint, crd_pt])

theorem pt_zero {Z : Over (Spec (CommRingCat.of k))} : (pt (0 : Γ(Z.left, ⊤)) : Z ⟶ (Ga k).X) = 1 :=
  crd_injective (by
    rw [crd_pt, crd, map_one]
    rfl)

/-- The orbit extension of a point `y` on a line `x`: `(z, s) ↦ x(s · y(z))`. -/
def lineOrbitExtension (x : Ga k ⟶ H) {Z : Over (Spec (CommRingCat.of k))}
    (y : Z ⟶ (Ga k).X) : Z ⊗ AffineLine.scheme (Spec (CommRingCat.of k)) ⟶ H.X :=
  pt ((fst Z _).left.appTop (crd y) * AffineLine.homEquiv _ (snd Z _)) ≫ x.hom.hom

/-- **Equivariant lines lie in root subgroups.** A torus-equivariant line of weight `a` lies
in the relative root subgroup functor of `a`, for any commutative group mapping to `H`. -/
theorem range_le_subgroup_of_isTorusEquivariant (t : T.toGrp ⟶ H) (a : characterLattice T)
    (x : Ga k ⟶ H) (hx : IsTorusEquivariant t x a) :
    SubgroupFunctor.range x ≤ RelativeRoot.subgroup t a := by
  intro Z g hg
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hg
  refine ⟨lineOrbitExtension x y, ?_, ?_⟩
  · rw [RelativeRoot.IsOrbitExtension, RelativeRoot.orbit, AutomorphicAction.conjugation_act]
    have hy : fst Z T.X ≫ y = scalarPoint (CommRingCat.of k) _ (crd (fst Z T.X ≫ y)) := by
      rw [scalarPoint_eq_pt]
      exact crd_injective (by rw [crd_pt])
    rw [← Category.assoc, hy, hx, lineOrbitExtension, ← Category.assoc]
    congr 1
    rw [scalarPoint_eq_pt]
    apply crd_injective
    have h1 : (Z ◁ ((CommGroupScheme.groupHom a).hom.hom ≫
        AffineLine.unitInclusion (Spec (CommRingCat.of k)))).left.appTop
          ((fst Z _).left.appTop (crd y)) = crd (fst Z T.X ≫ y) := by
      rw [crd_comp, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Over.comp_left,
        whiskerLeft_fst]
    have h2 : (Z ◁ ((CommGroupScheme.groupHom a).hom.hom ≫
        AffineLine.unitInclusion (Spec (CommRingCat.of k)))).left.appTop
          (AffineLine.homEquiv _ (snd Z _)) = charValue a _ (snd Z T.X) := by
      rw [← AffineLine.homEquiv_comp, whiskerLeft_snd, ← Category.assoc,
        AffineLine.homEquiv_comp_unitInclusion]
      rfl
    rw [crd_comp, crd_pt, crd_pt, map_mul, h1, h2, mul_comm]
  · have h3 : (lift (𝟙 Z) (toUnit Z ≫ AffineLine.zeroSection (Spec (CommRingCat.of k)))).left.appTop
        (AffineLine.homEquiv _ (snd Z _)) = 0 := by
      rw [← AffineLine.homEquiv_comp, lift_snd, AffineLine.homEquiv_comp, AffineLine.zeroSection,
        Equiv.apply_symm_apply, map_zero]
    have h4 : lift (𝟙 Z) (toUnit Z ≫ AffineLine.zeroSection (Spec (CommRingCat.of k))) ≫
        (pt ((fst Z _).left.appTop (crd y) * AffineLine.homEquiv _ (snd Z _)) :
          Z ⊗ AffineLine.scheme _ ⟶ (Ga k).X) = pt 0 :=
      crd_injective (by rw [crd_comp, crd_pt, map_mul, h3, mul_zero, crd_pt])
    rw [Dynamic.evalZero, lineOrbitExtension, ← Category.assoc, h4, pt_zero, MonObj.one_comp]

end Lines

section Closure

variable {k : Type u} [Field k] [IsAlgClosed k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {H : GroupScheme (Spec (CommRingCat.of k))}

/-- The rational points of the range of a homomorphism. -/
abbrev rangePts {M : GroupScheme (Spec (CommRingCat.of k))} (f : M ⟶ H) : Subgroup (rationalPoints H) :=
  (SubgroupFunctor.range f).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k))))

/-- In an irreducible group scheme locally of finite type over an algebraically closed
field, every rational point lies in the closure of the rational points located in a fixed
nonempty open subset. -/
theorem rationalPointClosure_located_eq_univ {P : GroupScheme (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType P.X.hom] [IrreducibleSpace P.X.left] (U : P.X.left.Opens)
    (hU : (U : Set P.X.left).Nonempty) :
    rationalPointClosure P {p | p.left (IsLocalRing.closedPoint k) ∈ U} = Set.univ := by
  have : JacobsonSpace P.X.left := LocallyOfFiniteType.jacobsonSpace P.X.hom
  have hd : Dense (rationalPointImage P {p | p.left (IsLocalRing.closedPoint k) ∈ U}) := by
    refine dense_iff_inter_open.mpr fun W hW hne => ?_
    have hWU : (W ∩ U).Nonempty := (U.isOpen.dense hU).inter_open_nonempty W hW hne
    obtain ⟨y, ⟨hyW, hyU⟩, hyclosed⟩ :=
      nonempty_inter_closedPoints hWU (hW.inter U.isOpen).isLocallyClosed
    let p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P.X :=
      Over.homMk (pointOfClosedPoint P.X.hom y hyclosed)
        (pointOfClosedPoint_comp P.X.hom y hyclosed)
    have hp : p.left (IsLocalRing.closedPoint k) = y := pointOfClosedPoint_apply _ _ _ _
    refine ⟨y, hyW, p, ?_, hp⟩
    change p.left (IsLocalRing.closedPoint k) ∈ U
    rw [hp]
    exact hyU
  refine Set.eq_univ_of_forall fun x => ?_
  change x.left (IsLocalRing.closedPoint k) ∈ closure (rationalPointImage P _)
  rw [hd.closure_eq]
  exact Set.mem_univ _

omit [IsAlgClosed k] in
theorem locallyOfFiniteType_vectorGroup (d : ℕ) :
    LocallyOfFiniteType (VectorGroup.groupScheme (CommRingCat.of k) d).X.hom := by
  change LocallyOfFiniteType
    (Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin d) k))))
  apply HasRingHomProperty.Spec_iff.mpr
  exact RingHom.finiteType_algebraMap.mpr inferInstance

/-- The product map `(X, Y) ↦ x(X) y(Y)` on the plane. -/
def planeProduct (x y : Ga k ⟶ H) : (Universal.plane k) ⟶ H.X :=
  (pt (Universal.cX k) ≫ x.hom.hom) * (pt (Universal.cY k) ≫ y.hom.hom)

omit [IsAlgClosed k] in
theorem comp_pt {Z Z' : Over (Spec (CommRingCat.of k))} (w : Z' ⟶ Z) (c : Γ(Z.left, ⊤)) :
    w ≫ (pt c : Z ⟶ (Ga k).X) = pt (w.left.appTop c) :=
  crd_injective (by rw [crd_comp, crd_pt, crd_pt])

omit [IsAlgClosed k] in
theorem comp_planeProduct (x y : Ga k ⟶ H) {Z : Over (Spec (CommRingCat.of k))}
    (q : Z ⟶ Universal.plane k) :
    q ≫ planeProduct x y = (pt (q.left.appTop (Universal.cX k)) ≫ x.hom.hom) *
      (pt (q.left.appTop (Universal.cY k)) ≫ y.hom.hom) := by
  rw [planeProduct, MonObj.comp_mul, ← Category.assoc, ← Category.assoc, comp_pt, comp_pt]

omit [IsAlgClosed k] in
/-- Every rational point of the three-factor cell is a product of rational points. -/
theorem comp_tripleCell_mem (t : T.toGrp ⟶ H) (x y : Ga k ⟶ H)
    (c : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ (Ga k).X ⊗ (T.X ⊗ (Ga k).X)) :
    c ≫ Dynamic.tripleCellMultiplication y t x ∈
      (rangePts y : Set (rationalPoints H)) * (rangePts t : Set (rationalPoints H)) * (rangePts x : Set (rationalPoints H)) := by
  have hsplit : c = lift (c ≫ fst _ _) (lift (c ≫ snd _ _ ≫ fst _ _) (c ≫ snd _ _ ≫ snd _ _)) := by
    ext1
    · rw [lift_fst]
    · ext1
      · rw [lift_snd, lift_fst, Category.assoc]
      · rw [lift_snd, lift_snd, Category.assoc]
  rw [hsplit, Dynamic.lift_tripleCellMultiplication, ← mul_assoc]
  refine Set.mul_mem_mul (Set.mul_mem_mul ?_ ?_) ?_
  · exact SubgroupFunctor.mem_range.mpr ⟨_, rfl⟩
  · exact SubgroupFunctor.mem_range.mpr ⟨_, rfl⟩
  · exact SubgroupFunctor.mem_range.mpr ⟨_, rfl⟩

omit [IsAlgClosed k] in
/-- A rational point of the plane located in `1 + XY ≠ 0` has `1 + XY` a unit. -/
theorem isUnit_of_mem_openU (q : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Universal.plane k)
    (hq : q.left (IsLocalRing.closedPoint k) ∈ Universal.openU k) :
    IsUnit (q.left.appTop (1 + Universal.cX k * Universal.cY k)) := by
  apply isUnit_of_basicOpen_eq_top
  rw [← Scheme.preimage_basicOpen_top]
  apply eq_top_iff.2
  intro z _
  have : Subsingleton (Over.mk (𝟙 (Spec (CommRingCat.of k)))).left :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  rw [Subsingleton.elim z (IsLocalRing.closedPoint k)]
  exact hq

omit [IsAlgClosed k] in
/-- Plane points in `1 + XY ≠ 0` map into the rational cell. -/
theorem comp_planeProduct_mem (t : T.toGrp ⟶ H) (ν : cocharacterLattice T) (x y : Ga k ⟶ H)
    (hrel : RelationOver t ν x y (Over.mk (𝟙 (Spec (CommRingCat.of k)))))
    (q : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Universal.plane k)
    (hq : q.left (IsLocalRing.closedPoint k) ∈ Universal.openU k) :
    q ≫ planeProduct x y ∈
      (rangePts y : Set (rationalPoints H)) * (rangePts t : Set (rationalPoints H)) * (rangePts x : Set (rationalPoints H)) := by
  have hunit : IsUnit (1 + crd (pt (q.left.appTop (Universal.cX k)) :
      Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ (Ga k).X) *
        crd (pt (q.left.appTop (Universal.cY k)) :
          Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ (Ga k).X)) := by
    rw [crd_pt, crd_pt]
    simpa only [map_add, map_mul, map_one] using isUnit_of_mem_openU q hq
  obtain ⟨c, hc⟩ := inCell_of_relationOver hrel _ _ hunit
  rw [comp_planeProduct, ← hc]
  exact comp_tripleCell_mem t x y c

/-- **Rank-one closure.** If the rank-one relation holds for rational points, then every
product `x(s) y(r)` of rational points lies in the closure of the rational products
`y(·) t(·) x(·)`. This is the pair condition of the generated-density argument. -/
theorem pair_subset_rationalPointClosure [LocallyOfFiniteType H.X.hom]
    (t : T.toGrp ⟶ H) (ν : cocharacterLattice T) (x y : Ga k ⟶ H)
    (hrel : RelationOver t ν x y (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :
    (rangePts x : Set (rationalPoints H)) * (rangePts y : Set (rationalPoints H)) ⊆
      rationalPointClosure H
        ((rangePts y : Set (rationalPoints H)) * (rangePts t : Set (rationalPoints H)) * (rangePts x : Set (rationalPoints H))) := by
  rintro _ ⟨g1, hg1, g2, hg2, rfl⟩
  obtain ⟨s, rfl⟩ := SubgroupFunctor.mem_range.mp hg1
  obtain ⟨r, rfl⟩ := SubgroupFunctor.mem_range.mp hg2
  let q : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Universal.plane k :=
    (VectorGroup.coordinates (CommRingCat.of k) 2 _).symm (Multiplicative.ofAdd ![crd s, crd r])
  have hqX : q.left.appTop (Universal.cX k) = crd s := by
    rw [Universal.cX, ← VectorGroup.coordinates_apply, MulEquiv.apply_symm_apply, toAdd_ofAdd]
    rfl
  have hqY : q.left.appTop (Universal.cY k) = crd r := by
    rw [Universal.cY, ← VectorGroup.coordinates_apply, MulEquiv.apply_symm_apply, toAdd_ofAdd]
    rfl
  have heq : (s ≫ x.hom.hom) * (r ≫ y.hom.hom) = q ≫ planeProduct x y := by
    rw [comp_planeProduct, hqX, hqY]
    congr 2
    · exact crd_injective (by rw [crd_pt])
    · exact crd_injective (by rw [crd_pt])
  beta_reduce
  rw [heq]
  have hne : ((Universal.openU k : (Universal.plane k).left.Opens) :
      Set (Universal.plane k).left).Nonempty := by
    obtain ⟨z⟩ := Universal.nonempty_openU k
    exact ⟨z.1, z.2⟩
  have := locallyOfFiniteType_vectorGroup (k := k) 2
  have hall := rationalPointClosure_located_eq_univ
    (P := VectorGroup.groupScheme (CommRingCat.of k) 2) _ hne
  refine LeviGluing.postcomp_mem_rationalPointClosure (K := VectorGroup.groupScheme _ 2)
    (S := {p | p.left (IsLocalRing.closedPoint k) ∈ Universal.openU k}) (planeProduct x y)
    (fun q' hq' => subset_rationalPointClosure _ (comp_planeProduct_mem t ν x y hrel q' hq')) ?_
  rw [hall]
  exact Set.mem_univ q

end Closure

section Density

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {H : GroupScheme (Spec (CommRingCat.of k))}

/-- Torus points normalize the rational points of an equivariant line. -/
theorem conj_mem_rangePts_of_isTorusEquivariant (t : T.toGrp ⟶ H) (a : characterLattice T)
    (x : Ga k ⟶ H) (hx : IsTorusEquivariant t x a) {g h : rationalPoints H} (hg : g ∈ rangePts t)
    (hh : h ∈ rangePts x) : g * h * g⁻¹ ∈ rangePts x := by
  obtain ⟨s, rfl⟩ := SubgroupFunctor.mem_range.mp hg
  obtain ⟨p, rfl⟩ := SubgroupFunctor.mem_range.mp hh
  have hp : p = scalarPoint (CommRingCat.of k) _ (crd p) := by
    rw [scalarPoint_eq_pt]
    exact crd_injective (by rw [crd_pt])
  rw [hp, hx]
  exact SubgroupFunctor.mem_range.mpr ⟨_, rfl⟩

/-- A subgroup conjugating a set into itself normalizes the subgroup it generates. -/
theorem le_normalizer_closure {Γ : Type*} [Group Γ] (P : Subgroup Γ) (S : Set Γ)
    (hS : ∀ g ∈ P, ∀ h ∈ S, g * h * g⁻¹ ∈ S) :
    P ≤ Subgroup.normalizer (Subgroup.closure S : Set Γ) := by
  have key : ∀ g ∈ P, ∀ h ∈ Subgroup.closure S, g * h * g⁻¹ ∈ Subgroup.closure S := by
    intro g hg h hh
    induction hh using Subgroup.closure_induction with
    | mem h hh => exact Subgroup.subset_closure (hS g hg h hh)
    | one => simp
    | mul a b _ _ ha hb =>
      have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [e]
      exact mul_mem ha hb
    | inv a _ ha =>
      have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem ha
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨key g hg h, fun hh => ?_⟩
  have h' := key g⁻¹ (inv_mem hg) _ hh
  have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
  rwa [e] at h'

/-- The rational points generated by a family of lines. -/
abbrev generatedPts {Idx : Type*} (x : Idx → (Ga k ⟶ H)) : Subgroup (rationalPoints H) :=
  Subgroup.closure (⋃ i, (rangePts (x i) : Set (rationalPoints H)))

/-- **Density of the generated cell** (CGP C.2.29, Step 1, on rational points). Lines
`x i` of weights `a i` and `y i` of weights `-a i`, with the rank-one relation for each `i`
and with `x i` commuting with `y j` for `i ≠ j`, whose rational points together with the
torus generate a dense subgroup, give a dense set `V · T · U` of rational products, where
`U` and `V` are generated by the rational points of the `x i` and the `y i`. -/
theorem dense_generatedCell [IsAlgClosed k] [LocallyOfFiniteType H.X.hom] {Idx : Type*}
    (t : T.toGrp ⟶ H) (a : Idx → characterLattice T) (ν : Idx → cocharacterLattice T)
    (x y : Idx → (Ga k ⟶ H))
    (hx : ∀ i, IsTorusEquivariant t (x i) (a i)) (hy : ∀ i, IsTorusEquivariant t (y i) (-a i))
    (hrel : ∀ i, RelationOver t (ν i) (x i) (y i) (Over.mk (𝟙 (Spec (CommRingCat.of k)))))
    (hcomm : ∀ i j, i ≠ j → ∀ g ∈ rangePts (x i), ∀ h ∈ rangePts (y j), Commute g h)
    (hgen : Dense (rationalPointImage H (Subgroup.closure
      ((⋃ i, (rangePts (x i) : Set (rationalPoints H))) ∪ (⋃ i, (rangePts (y i) : Set (rationalPoints H))) ∪
        (rangePts t : Set (rationalPoints H))) : Set (rationalPoints H)))) :
    Dense (rationalPointImage H ((generatedPts y : Set (rationalPoints H)) * (rangePts t : Set (rationalPoints H)) *
      (generatedPts x : Set (rationalPoints H)))) := by
  have hnorm : ∀ (z : Idx → (Ga k ⟶ H)) (c : Idx → characterLattice T),
      (∀ i, IsTorusEquivariant t (z i) (c i)) →
        rangePts t ≤ Subgroup.normalizer (generatedPts z : Set (rationalPoints H)) := by
    intro z c hz
    apply le_normalizer_closure
    intro g hg h hh
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hh
    exact Set.mem_iUnion.mpr ⟨i, conj_mem_rangePts_of_isTorusEquivariant t _ (z i) (hz i) hg hi⟩
  refine LeviGluing.dense_rationalPointImage_tripleProduct H (fun i => rangePts (x i))
    (fun i => rangePts (y i)) (generatedPts y) (rangePts t) (generatedPts x)
    (fun i g hg => Subgroup.subset_closure (Set.mem_iUnion.mpr ⟨i, hg⟩)) rfl
    (hnorm y _ hy) (hnorm x _ hx) hcomm
    (fun i => pair_subset_rationalPointClosure t (ν i) (x i) (y i) (hrel i)) ?_
  have heq : Subgroup.closure ((⋃ i, (rangePts (x i) : Set (rationalPoints H))) ∪
      (generatedPts y : Set (rationalPoints H)) ∪ (rangePts t : Set (rationalPoints H))) =
      Subgroup.closure ((⋃ i, (rangePts (x i) : Set (rationalPoints H))) ∪
        (⋃ i, (rangePts (y i) : Set (rationalPoints H))) ∪ (rangePts t : Set (rationalPoints H))) := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro g ((hg | hg) | hg)
      · exact Subgroup.subset_closure (Or.inl (Or.inl hg))
      · exact (Subgroup.closure_mono (fun z hz => Or.inl (Or.inr hz)) :
          generatedPts y ≤ _) hg
      · exact Subgroup.subset_closure (Or.inr hg)
    · exact Subgroup.closure_mono (Set.union_subset_union_left _
        (Set.union_subset_union_right _ Subgroup.subset_closure))
  rw [heq]
  exact hgen

/-- A commutative group lies in the dynamic centralizer of each of its cocharacters. -/
theorem range_le_centralizer_cocharacter (t : T.toGrp ⟶ H) (cch : cocharacterLattice T) :
    SubgroupFunctor.range t ≤ Dynamic.centralizer (CommGroupScheme.groupHom cch ≫ t) := by
  intro Z g hg
  obtain ⟨p, rfl⟩ := SubgroupFunctor.mem_range.mp hg
  rw [Dynamic.mem_centralizer, Dynamic.orbit]
  have hc : Commute (snd Z _ ≫ (CommGroupScheme.groupHom cch ≫ t).hom.hom)
      (fst Z _ ≫ p ≫ t.hom.hom) := by
    rw [Grp.comp_hom_hom, ← Category.assoc, ← Category.assoc, Commute, SemiconjBy,
      ← MonObj.mul_comp, ← MonObj.mul_comp, mul_comm]
  exact hc.mul_inv_cancel

/-- **Dynamic factors of the generated group** (CGP C.2.29, Step 1). Under the hypotheses of
`dense_generatedCell`, closed subgroups `n`, `u` inside the opposite and positive dynamic
unipotent factors of a cocharacter, containing the rational points of the `y i` and the
`x i` respectively, represent those factors, and the torus represents the centralizer. -/
theorem isRepresentedBy_dynamicFactors_of_generated [IsAlgClosed k] [Smooth H.X.hom]
    [IsAffineHom H.X.hom] {Idx : Type*}
    (t : T.toGrp ⟶ H) (a : Idx → characterLattice T) (ν : Idx → cocharacterLattice T)
    (x y : Idx → (Ga k ⟶ H))
    (hx : ∀ i, IsTorusEquivariant t (x i) (a i)) (hy : ∀ i, IsTorusEquivariant t (y i) (-a i))
    (hrel : ∀ i, RelationOver t (ν i) (x i) (y i) (Over.mk (𝟙 (Spec (CommRingCat.of k)))))
    (hcomm : ∀ i j, i ≠ j → ∀ g ∈ rangePts (x i), ∀ h ∈ rangePts (y j), Commute g h)
    (hgen : Dense (rationalPointImage H (Subgroup.closure
      ((⋃ i, (rangePts (x i) : Set (rationalPoints H))) ∪ (⋃ i, (rangePts (y i) : Set (rationalPoints H))) ∪
        (rangePts t : Set (rationalPoints H))) : Set (rationalPoints H))))
    (cch : cocharacterLattice T) (ht : IsClosedSubgroup t)
    {N U : GroupScheme (Spec (CommRingCat.of k))} (n : N ⟶ H) (u : U ⟶ H)
    (hn : IsClosedSubgroup n) (hu : IsClosedSubgroup u)
    (hnle : SubgroupFunctor.range n ≤ Dynamic.unipotent
      (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫
        CommGroupScheme.groupHom cch ≫ t))
    (hule : SubgroupFunctor.range u ≤ Dynamic.unipotent (CommGroupScheme.groupHom cch ≫ t))
    (hyn : ∀ i, rangePts (y i) ≤ rangePts n) (hxu : ∀ i, rangePts (x i) ≤ rangePts u) :
    (Dynamic.unipotent (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫
        CommGroupScheme.groupHom cch ≫ t)).IsRepresentedBy n ∧
      (Dynamic.centralizer (CommGroupScheme.groupHom cch ≫ t)).IsRepresentedBy t ∧
        (Dynamic.unipotent (CommGroupScheme.groupHom cch ≫ t)).IsRepresentedBy u := by
  have hsub : (generatedPts y : Set (rationalPoints H)) * (rangePts t : Set (rationalPoints H)) *
      (generatedPts x : Set (rationalPoints H)) ⊆ LeviGluing.rationalTripleProduct n t u := by
    rw [LeviGluing.rationalTripleProduct_eq]
    refine Set.mul_subset_mul (Set.mul_subset_mul ?_ le_rfl) ?_
    · exact (Subgroup.closure_le _).mpr (Set.iUnion_subset fun i => hyn i)
    · exact (Subgroup.closure_le _).mpr (Set.iUnion_subset fun i => hxu i)
  refine LeviGluing.isRepresentedBy_dynamicFactors_of_dense_closed_subcell _ n t u hn ht hu hnle
    (range_le_centralizer_cocharacter t cch) hule ?_
  refine (dense_generatedCell t a ν x y hx hy hrel hcomm hgen).mono ?_
  rintro _ ⟨p, hp, rfl⟩
  exact ⟨p, hsub hp, rfl⟩

end Density

section Centralizer

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {H : GroupScheme (Spec (CommRingCat.of k))}

/-- Points centralizing the torus centralize each of its cocharacters. -/
theorem torusCentralizer_le_centralizer_cocharacter (t : T.toGrp ⟶ H)
    (cch : cocharacterLattice T) :
    torusCentralizer t ≤ Dynamic.centralizer (CommGroupScheme.groupHom cch ≫ t) := by
  intro U g hg
  rw [Dynamic.mem_centralizer]
  have h := hg (U ⊗ (Gm (Spec (CommRingCat.of k))).X) (fst _ _)
    (snd _ _ ≫ (CommGroupScheme.groupHom cch).hom.hom)
  have hc : snd U (Gm (Spec (CommRingCat.of k))).X ≫ (CommGroupScheme.groupHom cch ≫ t).hom.hom =
      (snd _ _ ≫ (CommGroupScheme.groupHom cch).hom.hom) ≫ t.hom.hom := by
    rw [Grp.comp_hom_hom, Category.assoc]
  rw [Dynamic.orbit, hc, ← h.eq, mul_assoc, mul_inv_cancel, mul_one]

/-- A commutative group lies in its own torus centralizer. -/
theorem range_le_torusCentralizer (t : T.toGrp ⟶ H) :
    SubgroupFunctor.range t ≤ torusCentralizer t := by
  intro U g hg V b s
  obtain ⟨p, rfl⟩ := SubgroupFunctor.mem_range.mp hg
  rw [Commute, SemiconjBy, ← Category.assoc, ← MonObj.mul_comp, ← MonObj.mul_comp, mul_comm]

/-- The opposite of a cocharacter, as precomposition with inversion. -/
theorem groupHom_neg_comp (t : T.toGrp ⟶ H) (cch : cocharacterLattice T) :
    CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫
        CommGroupScheme.groupHom cch ≫ t = CommGroupScheme.groupHom (-cch) ≫ t := by
  have heta : Gm.powerHom (Spec (CommRingCat.of k)) (-1) ≫ cch = -cch := by
    simp only [Gm.powerHom_apply, neg_one_zsmul, Preadditive.neg_comp, Category.id_comp]
  rw [← Category.assoc, ← heta]
  rfl

/-- **The torus is its own centralizer in the generated group** (CGP C.2.29(i)). Under the
hypotheses of `dense_generatedCell`, if a cocharacter pairs positively with every `a i` and
the torus is closed, then the torus centralizer is the torus. -/
theorem torusCentralizer_eq_range_of_generated [IsAlgClosed k] [Smooth H.X.hom]
    [IsAffineHom H.X.hom] {Idx : Type*}
    (t : T.toGrp ⟶ H) (a : Idx → characterLattice T) (ν : Idx → cocharacterLattice T)
    (x y : Idx → (Ga k ⟶ H))
    (hx : ∀ i, IsTorusEquivariant t (x i) (a i)) (hy : ∀ i, IsTorusEquivariant t (y i) (-a i))
    (hrel : ∀ i, RelationOver t (ν i) (x i) (y i) (Over.mk (𝟙 (Spec (CommRingCat.of k)))))
    (hcomm : ∀ i j, i ≠ j → ∀ g ∈ rangePts (x i), ∀ h ∈ rangePts (y j), Commute g h)
    (hgen : Dense (rationalPointImage H (Subgroup.closure
      ((⋃ i, (rangePts (x i) : Set (rationalPoints H))) ∪ (⋃ i, (rangePts (y i) : Set (rationalPoints H))) ∪
        (rangePts t : Set (rationalPoints H))) : Set (rationalPoints H))))
    (cch : cocharacterLattice T) (hpos : ∀ i, 0 < latticePairing T (a i) cch)
    (ht : IsClosedSubgroup t) :
    torusCentralizer t = SubgroupFunctor.range t := by
  let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  let χ := CommGroupScheme.groupHom cch ≫ t
  let χn := CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ
  have hn := Dynamic.Affine.isRepresentedBy_unipotentHom χn
  have hu := Dynamic.Affine.isRepresentedBy_unipotentHom χ
  have hrep := (isRepresentedBy_dynamicFactors_of_generated t a ν x y hx hy hrel hcomm hgen cch
    ht (Dynamic.Affine.unipotentHom χn) (Dynamic.Affine.unipotentHom χ)
    (Dynamic.Affine.isClosedSubgroup_unipotentHom χn)
    (Dynamic.Affine.isClosedSubgroup_unipotentHom χ) hn.2.le hu.2.le ?_ ?_).2.1
  · exact le_antisymm ((torusCentralizer_le_centralizer_cocharacter t cch).trans hrep.2.symm.le)
      (range_le_torusCentralizer t)
  · intro i g hg
    show g ∈ (SubgroupFunctor.range (Dynamic.Affine.unipotentHom χn)).carrier _
    rw [hn.2, show χn = CommGroupScheme.groupHom (-cch) ≫ t from groupHom_neg_comp t cch]
    have hp : 0 < latticePairing T (-a i) (-cch) := by
      simpa only [map_neg, LinearMap.neg_apply, neg_neg] using hpos i
    exact RelativeRoot.subgroup_le_dynamicUnipotent t (-cch) hp _
      (range_le_subgroup_of_isTorusEquivariant t _ (y i) (hy i) _ hg)
  · intro i g hg
    show g ∈ (SubgroupFunctor.range (Dynamic.Affine.unipotentHom χ)).carrier _
    rw [hu.2]
    exact RelativeRoot.subgroup_le_dynamicUnipotent t cch (hpos i) _
      (range_le_subgroup_of_isTorusEquivariant t _ (x i) (hx i) _ hg)

end Centralizer

end Langlands.GroupScheme.MaximalSplitSubgroup
