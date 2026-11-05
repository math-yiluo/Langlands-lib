import Langlands.GroupScheme.Rational.AdditiveGroupQuotient
import Langlands.GroupScheme.LinearAdditiveExtension.DiagonalizableAverage

/-! # The additive polynomial of a closed subgroup of the additive group -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Polynomial
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ClosedAdditivePolynomial

open RelativeRoot RelativeRoot.AdditiveGroupQuotient PointedCoordinateWeights

variable {k : Type u} [Field k]

local notation "𝔾ₐ" => VectorGroup.groupScheme (CommRingCat.of k) 1

/-- The vector coordinates of the additive group. -/
abbrev ga : ∀ T : Over (Spec (CommRingCat.of k)),
    (T ⟶ (𝔾ₐ).X) ≃* Multiplicative (Fin 1 → Γ(T.left, ⊤)) :=
  VectorGroup.coordinates (CommRingCat.of k) 1

theorem ga_comp : ∀ (T T' : Over (Spec (CommRingCat.of k))) (b : T' ⟶ T) (x : T ⟶ (𝔾ₐ).X),
    (ga T' (b ≫ x)).toAdd = fun j => b.left.appTop ((ga T x).toAdd j) :=
  fun _ _ b x => VectorGroup.coordinates_comp b x

variable {K : GroupScheme (Spec (CommRingCat.of k))} (a : K ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1)

/-- The ideal of the closed subgroup `a`, as an ideal of polynomials in the coordinate. -/
def closedIdeal : Ideal k[X] :=
  (RingHom.ker a.hom.hom.left.appTop.hom).comap (coordRingHom (ga (k := k)))

/-- The monic, or zero, generator of the ideal of the closed subgroup. -/
def closedPolynomial : k[X] :=
  Submodule.IsPrincipal.generator (closedIdeal a) *
    C (Submodule.IsPrincipal.generator (closedIdeal a)).leadingCoeff⁻¹

theorem closedIdeal_eq_span : closedIdeal a = Ideal.span {closedPolynomial a} := by
  conv_lhs => rw [← Ideal.span_singleton_generator (closedIdeal a)]
  by_cases h : Submodule.IsPrincipal.generator (closedIdeal a) = 0
  · rw [closedPolynomial, h, zero_mul]
  · rw [closedPolynomial, Ideal.span_singleton_mul_right_unit]
    exact isUnit_C.mpr (inv_ne_zero (leadingCoeff_ne_zero.mpr h)).isUnit

theorem closedPolynomial_monic (h : closedPolynomial a ≠ 0) : (closedPolynomial a).Monic := by
  have h' : Submodule.IsPrincipal.generator (closedIdeal a) ≠ 0 := by
    intro h0
    apply h
    rw [closedPolynomial, h0, zero_mul]
  exact monic_mul_leadingCoeff_inv h'

theorem ker_appTop_eq :
    RingHom.ker a.hom.hom.left.appTop.hom =
      Ideal.span {coordRingHom (ga (k := k)) (closedPolynomial a)} := by
  rw [← Ideal.map_comap_of_surjective _ (coordRingHom_bijective (ga (k := k)) ga_comp).2
    (RingHom.ker a.hom.hom.left.appTop.hom)]
  change Ideal.map (coordRingHom (ga (k := k))) (closedIdeal a) = _
  rw [closedIdeal_eq_span, Ideal.map_span, Set.image_singleton]

/-- A point lies in the closed subgroup exactly when the polynomial vanishes at its
coordinate. -/
theorem mem_range_iff_eval (ha : IsClosedSubgroup a) {T : Over (Spec (CommRingCat.of k))}
    (x : T ⟶ (𝔾ₐ).X) :
    x ∈ (SubgroupFunctor.range a).carrier T ↔
      (closedPolynomial a).eval₂ (structureMap T) (coord (ga (k := k)) x) = 0 := by
  have : IsAffine (𝔾ₐ).X.left := isAffine (ga (k := k)) ga_comp
  have : IsClosedImmersion a.hom.hom.left := ha
  have hI := ker_appTop_eq a
  rw [← appTop_coordRingHom (ga (k := k)) ga_comp x]
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    have hmem : coordRingHom (ga (k := k)) (closedPolynomial a) ∈
        RingHom.ker a.hom.hom.left.appTop.hom := by
      rw [hI]
      exact Ideal.subset_span rfl
    rw [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply,
      RingHom.mem_ker.mp hmem, map_zero]
  · intro h
    have hle : RingHom.ker a.hom.hom.left.appTop.hom ≤ RingHom.ker x.left.appTop.hom := by
      rw [hI, Ideal.span_le, Set.singleton_subset_iff]
      exact h
    have hker : a.hom.hom.left.ker ≤ x.left.ker := by
      rw [Scheme.ker_of_isAffine, Scheme.ker_of_isAffine]
      exact (map_le_map_iff (Scheme.IdealSheafData.equivOfIsAffine
        (X := (𝔾ₐ).X.left)).symm).mpr hle
    let y := IsClosedImmersion.lift a.hom.hom.left x.left hker
    have hy : y ≫ a.hom.hom.left = x.left := IsClosedImmersion.lift_fac _ _ _
    refine SubgroupFunctor.mem_range.mpr ⟨Over.homMk y ?_, Over.OverMorphism.ext hy⟩
    rw [← Over.w a.hom.hom, ← Category.assoc, hy, Over.w]

/-! ### Affine tests -/

variable (k) in
/-- The affine test scheme `Spec A` over `Spec k`. -/
abbrev affTest (A : Type u) [CommRing A] [Algebra k A] : Over (Spec (CommRingCat.of k)) :=
  (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) A))

section Affine

variable {A : Type u} [CommRing A] [Algebra k A]


theorem gammaHom_structureMap (c : k) :
    DiagonalizableAverage.gammaHom A (structureMap (affTest k A) c) = algebraMap k A c := by
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap k A))
  change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
    (Spec.map (CommRingCat.ofHom (algebraMap k A))).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom).hom c = _
  rw [h, Iso.inv_hom_id_assoc]
  rfl

theorem gammaHom_injective : Function.Injective (DiagonalizableAverage.gammaHom (k := k) A) :=
  (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).hom).1

theorem gammaHom_coord (x : Points (𝔾ₐ).X A) :
    DiagonalizableAverage.gammaHom A (coord (ga (k := k)) x) = DiagonalizableAverage.coord x :=
  rfl

theorem gammaHom_eval₂ (p : k[X]) (y : Γ((affTest k A).left, ⊤)) :
    DiagonalizableAverage.gammaHom A (p.eval₂ (structureMap (affTest k A)) y) =
      p.eval₂ (algebraMap k A) (DiagonalizableAverage.gammaHom A y) := by
  rw [Polynomial.hom_eval₂]
  congr 1
  ext c
  exact gammaHom_structureMap c

/-- The membership criterion on an affine test, in its coefficient algebra. -/
theorem mem_range_iff_eval_affine (ha : IsClosedSubgroup a) (x : Points (𝔾ₐ).X A) :
    x ∈ (SubgroupFunctor.range a).carrier (affTest k A) ↔
      (closedPolynomial a).eval₂ (algebraMap k A) (DiagonalizableAverage.coord x) = 0 := by
  rw [mem_range_iff_eval a ha, ← gammaHom_coord, ← gammaHom_eval₂,
    map_eq_zero_iff _ gammaHom_injective]

theorem eval_add_eq_zero (ha : IsClosedSubgroup a) {y z : A}
    (hy : (closedPolynomial a).eval₂ (algebraMap k A) y = 0)
    (hz : (closedPolynomial a).eval₂ (algebraMap k A) z = 0) :
    (closedPolynomial a).eval₂ (algebraMap k A) (y + z) = 0 := by
  have hy' := (mem_range_iff_eval_affine a ha (DiagonalizableAverage.ofCoord y)).mpr
    (by rwa [DiagonalizableAverage.coord_ofCoord])
  have hz' := (mem_range_iff_eval_affine a ha (DiagonalizableAverage.ofCoord z)).mpr
    (by rwa [DiagonalizableAverage.coord_ofCoord])
  have h := (mem_range_iff_eval_affine a ha _).mp (Subgroup.mul_mem _ hy' hz')
  rwa [DiagonalizableAverage.coord_mul, DiagonalizableAverage.coord_ofCoord,
    DiagonalizableAverage.coord_ofCoord] at h

end Affine

theorem algebraMap_poly_poly : algebraMap k k[X][X] = (C : k[X] →+* k[X][X]).comp C :=
  RingHom.ext fun c => by simp [Polynomial.algebraMap_apply]

/-- The universal pair of roots: `f(X + Y)` lies in `(f(X), f(Y))`. -/
theorem taylor_mem_span (ha : IsClosedSubgroup a) :
    taylor (X : k[X]) ((closedPolynomial a).map C) ∈
      Ideal.span {C (closedPolynomial a), (closedPolynomial a).map C} := by
  set f := closedPolynomial a
  set I : Ideal k[X][X] := Ideal.span {C f, f.map C}
  let B := k[X][X] ⧸ I
  let π : k[X][X] →ₐ[k] B := Ideal.Quotient.mkₐ k I
  have hev : ∀ y : k[X][X], f.eval₂ (algebraMap k B) (π y) =
      π (f.eval₂ (algebraMap k k[X][X]) y) := by
    intro y
    rw [← aeval_def, ← aeval_def, aeval_algHom_apply]
  have hX : f.eval₂ (algebraMap k k[X][X]) X = f.map C := by
    rw [algebraMap_poly_poly, ← eval₂_map, eval₂_C_X]
  have hCX : f.eval₂ (algebraMap k k[X][X]) (C X) = C f := by
    rw [algebraMap_poly_poly, ← Polynomial.hom_eval₂, eval₂_C_X]
  have h1 : f.eval₂ (algebraMap k B) (π X) = 0 := by
    rw [hev, hX]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have h2 : f.eval₂ (algebraMap k B) (π (C X)) = 0 := by
    rw [hev, hCX]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hab := eval_add_eq_zero (A := k[X][X] ⧸ I) a ha h1 h2
  rw [← map_add, hev] at hab
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change π _ = 0
  rw [← hab, taylor_apply]
  congr 1
  change (f.map C).eval₂ C (X + C X) = f.eval₂ (algebraMap k k[X][X]) (X + C X)
  rw [eval₂_map, algebraMap_poly_poly]

/-- The identity point lies in the closed subgroup, so `f(0) = 0`. -/
theorem eval_zero (ha : IsClosedSubgroup a) : (closedPolynomial a).eval 0 = 0 := by
  have h := (mem_range_iff_eval_affine a ha (A := k) 1).mp (Subgroup.one_mem _)
  rw [DiagonalizableAverage.coord_one, Algebra.algebraMap_self] at h
  exact h

theorem natDegree_pos (ha : IsClosedSubgroup a) (h : closedPolynomial a ≠ 0) :
    0 < (closedPolynomial a).natDegree := by
  rw [Nat.pos_iff_ne_zero]
  intro hd
  have hm := closedPolynomial_monic a h
  have h1 : closedPolynomial a = 1 := eq_one_of_monic_natDegree_zero hm hd
  have h0 := eval_zero a ha
  rw [h1, eval_one] at h0
  exact one_ne_zero h0

/-- A nonzero closed polynomial is additive in every commutative `k`-algebra. -/
theorem eval₂_add (ha : IsClosedSubgroup a) (h : closedPolynomial a ≠ 0)
    {S : Type*} [CommRing S] (ρ : k →+* S) (y z : S) :
    (closedPolynomial a).eval₂ ρ (y + z) =
      (closedPolynomial a).eval₂ ρ y + (closedPolynomial a).eval₂ ρ z :=
  AdditivePolynomial.eval₂_add_of_taylor_eq
    (AdditivePolynomial.taylor_eq_of_mem_span (closedPolynomial_monic a h)
      (natDegree_pos a ha h) (taylor_mem_span a ha)) ρ y z

/-! ### Scaling by a character -/

section Scaling

variable {S : CommGroupScheme (Spec (CommRingCat.of k))} [IsAffineHom S.X.hom]
  (χ : characterLattice S)

theorem algebraMap_polynomial (R : Type u) [CommRing R] [Algebra k R] :
    algebraMap k R[X] = (C : R →+* R[X]).comp (algebraMap k R) :=
  RingHom.ext fun c => by simp [Polynomial.algebraMap_apply]

theorem eval₂_algebraMap_eq_comp {R : Type u} [CommRing R] [Algebra k R] (p : k[X]) (q : R[X]) :
    p.eval₂ (algebraMap k R[X]) q = (p.map (algebraMap k R)).comp q := by
  rw [algebraMap_polynomial, Polynomial.comp, eval₂_map]

theorem pmap_universalPoint {A : Type u} [CommRing A] [Algebra k A] (d : Points S.X A) :
    DiagonalizableAverage.pmap (pointCoordinates d) (universalPoint S.X) = d := by
  apply pointCoordinates.injective
  rw [DiagonalizableAverage.pmap, pointCoordinates_naturality, coordinates_universalPoint,
    AlgHom.comp_id]

/-- The universal scaling identity `F(c₀ X) = c₀^N F(X)` over the coordinate algebra of `S`,
where `c₀` is the value of `χ` at the universal point. -/
theorem comp_C_mul_X_eq (ha : IsClosedSubgroup a) (h : closedPolynomial a ≠ 0)
    (hst : ∀ (T : Over (Spec (CommRingCat.of k))) (d : T ⟶ S.X)
      (x : T ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X),
      x ∈ (SubgroupFunctor.range a).carrier T →
        (VectorGroup.weightAction (n := 1) χ).act d x ∈ (SubgroupFunctor.range a).carrier T) :
    ((closedPolynomial a).map (algebraMap k (Coord S.X))).comp
        (C (DiagonalizableAverage.charCoeff χ (universalPoint S.X)) * X) =
      C (DiagonalizableAverage.charCoeff χ (universalPoint S.X) ^
          (closedPolynomial a).natDegree) *
        (closedPolynomial a).map (algebraMap k (Coord S.X)) := by
  set f := closedPolynomial a
  set R := (Coord S.X : Type u)
  set c₀ := DiagonalizableAverage.charCoeff χ (universalPoint S.X)
  set F := f.map (algebraMap k R)
  have : Nontrivial R :=
    (pointCoordinates (1 : Points S.X k) : R →+* k).domain_nontrivial
  have hf := closedPolynomial_monic a h
  have hF : F.Monic := hf.map _
  have hFdeg : F.natDegree = f.natDegree := hf.natDegree_map _
  set I : Ideal R[X] := Ideal.span {F}
  let π : R[X] →ₐ[k] R[X] ⧸ I := Ideal.Quotient.mkₐ k I
  let ψ : R →ₐ[k] R[X] ⧸ I := π.comp (IsScalarTower.toAlgHom k R R[X])
  have hev : ∀ q : R[X], f.eval₂ (algebraMap k (R[X] ⧸ I)) (π q) = π (F.comp q) := by
    intro q
    rw [← aeval_def, aeval_algHom_apply, aeval_def, eval₂_algebraMap_eq_comp]
  let d₁ : Points S.X (R[X] ⧸ I) := DiagonalizableAverage.pmap ψ (universalPoint S.X)
  let x₁ : Points (VectorGroup.groupScheme (CommRingCat.of k) 1).X (R[X] ⧸ I) :=
    DiagonalizableAverage.ofCoord (π X)
  have hx₁ : x₁ ∈ (SubgroupFunctor.range a).carrier (affTest k (R[X] ⧸ I)) := by
    rw [mem_range_iff_eval_affine a ha, DiagonalizableAverage.coord_ofCoord, hev, comp_X]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have hy := (mem_range_iff_eval_affine a ha _).mp (hst _ d₁ x₁ hx₁)
  rw [DiagonalizableAverage.coord_weightAction, DiagonalizableAverage.charCoeff_pmap,
    DiagonalizableAverage.coord_ofCoord] at hy
  have hψ : ψ c₀ * π X = π (C c₀ * X) := by
    rw [map_mul]
    rfl
  rw [hψ, hev] at hy
  have hmem : F.comp (C c₀ * X) ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hy
  set g := F.comp (C c₀ * X) - C (c₀ ^ f.natDegree) * F with hg
  have hgmem : g ∈ I := Ideal.sub_mem _ hmem (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))
  have hgdeg : g.degree < F.degree := by
    rw [degree_eq_natDegree hF.ne_zero, hFdeg, degree_lt_iff_coeff_zero]
    intro m hm
    rw [hg, coeff_sub, comp_C_mul_X_coeff, coeff_C_mul]
    rcases hm.lt_or_eq with hlt | heq
    · rw [coeff_eq_zero_of_natDegree_lt (by rw [hFdeg]; exact hlt), zero_mul, mul_zero,
        sub_zero]
    · rw [← heq, mul_comm, sub_self]
  have hg0 : g = 0 := by
    have h1 : g %ₘ F = 0 :=
      (modByMonic_eq_zero_iff_dvd hF).mpr (Ideal.mem_span_singleton.mp hgmem)
    rwa [(modByMonic_eq_self_iff hF).mpr hgdeg] at h1
  exact sub_eq_zero.mp hg0

/-- Scaling identity on affine tests: `f(χ(d) y) = χ(d)^N f(y)`. -/
theorem eval₂_charCoeff_mul (ha : IsClosedSubgroup a) (h : closedPolynomial a ≠ 0)
    (hst : ∀ (T : Over (Spec (CommRingCat.of k))) (d : T ⟶ S.X)
      (x : T ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X),
      x ∈ (SubgroupFunctor.range a).carrier T →
        (VectorGroup.weightAction (n := 1) χ).act d x ∈ (SubgroupFunctor.range a).carrier T)
    {A : Type u} [CommRing A] [Algebra k A] (d : Points S.X A) (y : A) :
    (closedPolynomial a).eval₂ (algebraMap k A) (DiagonalizableAverage.charCoeff χ d * y) =
      DiagonalizableAverage.charCoeff χ d ^ (closedPolynomial a).natDegree *
        (closedPolynomial a).eval₂ (algebraMap k A) y := by
  set θ := pointCoordinates d
  have hd : DiagonalizableAverage.charCoeff χ d =
      θ (DiagonalizableAverage.charCoeff χ (universalPoint S.X)) := by
    rw [← DiagonalizableAverage.charCoeff_pmap, pmap_universalPoint]
  have hθ : (θ : Coord S.X →+* A).comp (algebraMap k (Coord S.X)) = algebraMap k A :=
    θ.comp_algebraMap
  have key := congrArg (fun q => q.eval₂ (θ : Coord S.X →+* A) y) (comp_C_mul_X_eq a χ ha h hst)
  simp only [eval₂_comp, eval₂_mul, eval₂_C, eval₂_X, eval₂_map, hθ] at key
  rw [hd, ← map_pow]
  exact key

/-- Scaling identity on every test scheme: `f(χ(d) y) = χ(d)^N f(y)`. -/
theorem eval₂_charValue_mul (ha : IsClosedSubgroup a) (h : closedPolynomial a ≠ 0)
    (hst : ∀ (T : Over (Spec (CommRingCat.of k))) (d : T ⟶ S.X)
      (x : T ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X),
      x ∈ (SubgroupFunctor.range a).carrier T →
        (VectorGroup.weightAction (n := 1) χ).act d x ∈ (SubgroupFunctor.range a).carrier T)
    {T : Over (Spec (CommRingCat.of k))} (d : T ⟶ S.X) (y : Γ(T.left, ⊤)) :
    (closedPolynomial a).eval₂ (structureMap T) (VectorGroup.charValue χ T d * y) =
      VectorGroup.charValue χ T d ^ (closedPolynomial a).natDegree *
        (closedPolynomial a).eval₂ (structureMap T) y := by
  set R := (Coord S.X : Type u)
  let t : T ⟶ affTest k R := d ≫ (coordinateIso S.X).inv
  let θ : R →+* Γ(T.left, ⊤) :=
    t.left.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  have hθc : θ (DiagonalizableAverage.charCoeff χ (universalPoint S.X)) =
      VectorGroup.charValue χ T d := by
    have hd : d = t ≫ universalPoint S.X := by
      rw [universalPoint_eq_coordinateIso, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hd, VectorGroup.charValue_comp]
    change t.left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom _)) = _
    congr 1
    exact (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id_apply _
  have hθk : θ.comp (algebraMap k R) = structureMap T := by
    rw [← structureMap_comp t]
    ext c
    change t.left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (algebraMap k R c)) =
      t.left.appTop.hom (structureMap (affTest k R) c)
    congr 1
    have h1 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k R))
    change ((CommRingCat.ofHom (algebraMap k R)) ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).inv) c =
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (Spec.map (CommRingCat.ofHom (algebraMap k R))).appTop) c
    rw [h1]
  have key := congrArg (fun q => q.eval₂ θ y) (comp_C_mul_X_eq a χ ha h hst)
  simp only [eval₂_comp, eval₂_mul, eval₂_C, eval₂_X, eval₂_map, eval₂_pow, map_pow,
    hθc] at key
  rw [hθk] at key
  exact key

end Scaling

end Langlands.GroupScheme.ClosedAdditivePolynomial
