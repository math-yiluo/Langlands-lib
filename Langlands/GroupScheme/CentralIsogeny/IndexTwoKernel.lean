import Langlands.GroupScheme.Torus.HomKernelDiagonalizable
import Langlands.GroupScheme.Torus.DiagonalizableDecomposition
import Langlands.GroupScheme.CentralIsogeny.RestrictionIsomorphism
import Langlands.GroupScheme.CentralIsogeny.TorusRestriction
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof
import Langlands.Geometry.Building.CocharacterUniformizerProof

/-! # Central isogenies whose torus restriction has cocharacter index two

For a central isogeny `p : G ⟶ G'` over a field, with `G` connected reductive, and a commuting
square of split maximal tori `i : T ⟶ G`, `i' : T' ⟶ G'`, `t : T ⟶ T'` such that the image of
`X_*(T)` in `X_*(T')` has index two, the full scheme-theoretic kernel of `p` is `μ₂`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace IndexTwoKernel

/-! ### Lattice algebra -/

section Lattice

variable {M : Type*} [AddCommGroup M]

/-- Half of an integral linear form all of whose values are even. -/
def halfForm (f : M →ₗ[ℤ] ℤ) (h : ∀ x, (2 : ℤ) ∣ f x) : M →ₗ[ℤ] ℤ where
  toFun x := f x / 2
  map_add' x y := by
    rw [map_add]
    exact Int.add_ediv_of_dvd_left (h x)
  map_smul' c x := by
    rw [map_zsmul, smul_eq_mul, RingHom.id_apply, smul_eq_mul]
    exact Int.mul_ediv_assoc c (h x)

theorem two_mul_halfForm (f : M →ₗ[ℤ] ℤ) (h : ∀ x, (2 : ℤ) ∣ f x) (x : M) :
    2 * halfForm f h x = f x :=
  Int.mul_ediv_cancel' (h x)

variable {X Y X' Y' : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup X']
  [AddCommGroup Y']
  {P : X →ₗ[ℤ] Y →ₗ[ℤ] ℤ} {P' : X' →ₗ[ℤ] Y' →ₗ[ℤ] ℤ}
  {a : X' →+ X} {b : Y →ₗ[ℤ] Y'}

/-- In a quotient of order two, twice every element lies in the subgroup. -/
theorem two_smul_mem_range (hindex : Nat.card (Y' ⧸ LinearMap.range b) = 2) (n : Y') :
    (2 : ℤ) • n ∈ LinearMap.range b := by
  have h := card_nsmul_eq_zero' (G := Y' ⧸ LinearMap.range b)
    (x := Submodule.Quotient.mk n)
  rw [hindex, two_nsmul, ← Submodule.Quotient.mk_add,
    Submodule.Quotient.mk_eq_zero] at h
  rwa [two_smul]

/-- A quotient of order two has a nonzero class. -/
theorem exists_not_mem_range (hindex : Nat.card (Y' ⧸ LinearMap.range b) = 2) :
    ∃ n₀ : Y', n₀ ∉ LinearMap.range b := by
  obtain ⟨y, hy, -⟩ := (Nat.card_eq_two_iff' (0 : Y' ⧸ LinearMap.range b)).1 hindex
  obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact ⟨n, fun h => hy ((Submodule.Quotient.mk_eq_zero _).2 h)⟩

/-- In a quotient of order two, every class is zero or the class of a fixed nonzero element. -/
theorem mem_range_or_sub_mem_range (hindex : Nat.card (Y' ⧸ LinearMap.range b) = 2)
    {n₀ : Y'} (hn₀ : n₀ ∉ LinearMap.range b) (n : Y') :
    n ∈ LinearMap.range b ∨ n - n₀ ∈ LinearMap.range b := by
  by_cases hn : n ∈ LinearMap.range b
  · exact Or.inl hn
  · right
    obtain ⟨y, -, huniq⟩ :=
      (Nat.card_eq_two_iff' (0 : Y' ⧸ LinearMap.range b)).1 hindex
    have h₁ := huniq (Submodule.Quotient.mk n)
      (fun h => hn ((Submodule.Quotient.mk_eq_zero _).1 h))
    have h₂ := huniq (Submodule.Quotient.mk n₀)
      (fun h => hn₀ ((Submodule.Quotient.mk_eq_zero _).1 h))
    exact (Submodule.Quotient.eq _).1 (h₁.trans h₂.symm)

/-- The linear map `n ↦ b⁻¹(2n)`, defined when `b` is injective of index two. -/
def doubleLift (hb : Function.Injective b) (hindex : Nat.card (Y' ⧸ LinearMap.range b) = 2) :
    Y' →ₗ[ℤ] Y :=
  (LinearEquiv.ofInjective b hb).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict (LinearMap.range b) ((2 : ℤ) • LinearMap.id)
      (fun n => two_smul_mem_range hindex n)

theorem apply_doubleLift (hb : Function.Injective b)
    (hindex : Nat.card (Y' ⧸ LinearMap.range b) = 2) (n : Y') :
    b (doubleLift hb hindex n) = (2 : ℤ) • n := by
  simp only [doubleLift, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.ofInjective_symm_apply, LinearMap.codRestrict_apply]
  rfl

theorem doubleLift_apply_eq_of_apply (hb : Function.Injective b)
    (hindex : Nat.card (Y' ⧸ LinearMap.range b) = 2) {n : Y'} {m : Y}
    (h : b m = (2 : ℤ) • n) : doubleLift hb hindex n = m :=
  hb ((apply_doubleLift hb hindex n).trans h.symm)

/-- A perfect pairing makes its right lattice torsion free at two. -/
theorem eq_zero_of_two_smul_eq_zero (hP' : P'.IsPerfPair) {y : Y'} (hy : (2 : ℤ) • y = 0) :
    y = 0 := by
  apply (LinearMap.IsPerfPair.bijective_right P').1
  ext ψ
  have h : (2 : ℤ) * P' ψ y = 0 := by
    rw [← smul_eq_mul, ← map_zsmul, hy, map_zero]
  simpa using h

/-- The parity class. For an injective cocharacter map of index two, with adjoint pullback of
characters, the parity of the pairing with `b⁻¹(2n₀)` is a surjection onto `ZMod 2` with kernel
the image of character pullback. -/
theorem exists_parity (hP : P.IsPerfPair) (hP' : P'.IsPerfPair)
    (hab : ∀ χ ν, P' χ (b ν) = P (a χ) ν) (hb : Function.Injective b)
    (hindex : Nat.card (Y' ⧸ LinearMap.range b) = 2) :
    ∃ Φ : X →+ ZMod 2, Function.Surjective Φ ∧ Φ.ker = a.range := by
  obtain ⟨n₀, hn₀⟩ := exists_not_mem_range hindex
  set g := doubleLift hb hindex
  set m₀ := g n₀
  have hm₀ : b m₀ = (2 : ℤ) • n₀ := apply_doubleLift hb hindex n₀
  let Φ : X →+ ZMod 2 := (Int.castAddHom (ZMod 2)).comp (P.flip m₀).toAddMonoidHom
  have hΦ : ∀ χ, Φ χ = ((P χ m₀ : ℤ) : ZMod 2) := fun χ => rfl
  refine ⟨Φ, ?_, ?_⟩
  · -- some character has odd pairing with `m₀`
    have hodd : ∃ χ, ¬ (2 : ℤ) ∣ P χ m₀ := by
      by_contra hcon
      push Not at hcon
      let κ := halfForm (P.flip m₀) hcon
      obtain ⟨m₁, hm₁⟩ := (LinearMap.IsPerfPair.bijective_right P).2 κ
      have h2m₁ : (2 : ℤ) • m₁ = m₀ := by
        apply (LinearMap.IsPerfPair.bijective_right P).1
        ext χ
        have := two_mul_halfForm (P.flip m₀) hcon χ
        change P χ ((2 : ℤ) • m₁) = P χ m₀
        rw [map_zsmul, smul_eq_mul]
        have hκ : P χ m₁ = κ χ := by rw [← hm₁]; rfl
        rw [hκ]
        exact this
      apply hn₀
      refine ⟨m₁, ?_⟩
      have h0 : (2 : ℤ) • (b m₁ - n₀) = 0 := by
        rw [smul_sub, ← map_zsmul, h2m₁, hm₀, sub_self]
      exact sub_eq_zero.1 (eq_zero_of_two_smul_eq_zero hP' h0)
    obtain ⟨χ, hχ⟩ := hodd
    have hχ1 : Φ χ = 1 := by
      rw [hΦ]
      have hodd' : Odd (P χ m₀) := Int.not_even_iff_odd.1 (fun he => hχ (even_iff_two_dvd.1 he))
      obtain ⟨r, hr⟩ := hodd'
      rw [hr]
      push_cast
      rw [show ((2 : ZMod 2)) = 0 from rfl, zero_mul, zero_add]
    intro z
    fin_cases z
    · exact ⟨0, map_zero Φ⟩
    · exact ⟨χ, hχ1⟩
  · ext χ
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
    constructor
    · intro hχ
      have hdiv0 : (2 : ℤ) ∣ P χ m₀ := by
        rw [hΦ] at hχ
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).1 hχ
      -- evenness of `n ↦ P χ (g n)`
      have heven : ∀ n, (2 : ℤ) ∣ (P χ ∘ₗ g) n := by
        intro n
        rcases mem_range_or_sub_mem_range hindex hn₀ n with ⟨m, hm⟩ | ⟨m, hm⟩
        · have : g n = (2 : ℤ) • m :=
            doubleLift_apply_eq_of_apply hb hindex (by rw [map_zsmul, hm])
          refine ⟨P χ m, ?_⟩
          simp [this]
        · have : g n = m₀ + (2 : ℤ) • m := by
            apply doubleLift_apply_eq_of_apply hb hindex
            rw [map_add, map_zsmul, hm, hm₀, ← smul_add, add_sub_cancel]
          rw [LinearMap.comp_apply, this, map_add, map_zsmul, smul_eq_mul]
          exact dvd_add hdiv0 (dvd_mul_right 2 _)
      let lam := halfForm (P χ ∘ₗ g) heven
      obtain ⟨ψ, hψ⟩ := (LinearMap.IsPerfPair.bijective_left P').2 lam
      refine ⟨ψ, ?_⟩
      apply (LinearMap.IsPerfPair.bijective_left P).1
      ext ν
      rw [← hab]
      have hg : g (b ν) = (2 : ℤ) • ν :=
        doubleLift_apply_eq_of_apply hb hindex (map_zsmul b 2 ν)
      have h2 := two_mul_halfForm (P χ ∘ₗ g) heven (b ν)
      rw [LinearMap.comp_apply, hg, map_zsmul, smul_eq_mul] at h2
      have hl : P' ψ (b ν) = lam (b ν) := by rw [hψ]
      rw [hl]
      exact mul_left_cancel₀ two_ne_zero h2
    · rintro ⟨ψ, rfl⟩
      rw [hΦ, ← hab, hm₀, map_zsmul, smul_eq_mul]
      push_cast
      rw [show ((2 : ZMod 2)) = 0 from rfl, zero_mul]

end Lattice

/-! ### The torus kernel -/

section TorusKernel

variable {k : Type u} [Field k] {T T' : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Character pullback is adjoint to cocharacter pushforward for the actual pairing. -/
theorem latticePairing_cocharacterMapInt (t : T ⟶ T') (χ : characterLattice T')
    (ν : cocharacterLattice T) :
    latticePairing T' χ (RealTorusSpace.cocharacterMapInt t ν) =
      latticePairing T (characterLattice.comapHom (CommGroupScheme.groupHom t) χ) ν := by
  change gmEndEquiv k ((ν ≫ t) ≫ χ) = gmEndEquiv k (ν ≫ (t ≫ χ))
  rw [Category.assoc]

/-- If the cocharacter map is injective of index two, the character group of the full kernel
of the torus map is cyclic of order two. -/
theorem nonempty_homKernelLattice_addEquiv (t : T ⟶ T') (hT : IsSplitTorus T.toGrp)
    (hT' : IsSplitTorus T'.toGrp)
    (hb : Function.Injective (RealTorusSpace.cocharacterMapInt t))
    (hindex : Nat.card (cocharacterLattice T' ⧸
      LinearMap.range (RealTorusSpace.cocharacterMapInt t)) = 2) :
    Nonempty (Diagonalizable.homKernelLattice (CommGroupScheme.groupHom t) ≃+
      ULift.{u} (ZMod 2)) := by
  obtain ⟨Φ, hΦ, hker⟩ := exists_parity
    (CocharacterUniformizer.latticePairing_isPerfPair k T hT)
    (CocharacterUniformizer.latticePairing_isPerfPair k T' hT')
    (a := characterLattice.comapHom (CommGroupScheme.groupHom t))
    (latticePairing_cocharacterMapInt t) hb hindex
  exact ⟨(QuotientAddGroup.quotientAddEquivOfEq hker.symm).trans
    ((QuotientAddGroup.quotientKerEquivOfSurjective Φ hΦ).trans AddEquiv.ulift.symm)⟩

/-- A chosen identification of the kernel character group with `ZMod 2`. It is unique, since
`ZMod 2` has no nontrivial additive automorphism. -/
def homKernelLatticeEquiv (t : T ⟶ T') (hT : IsSplitTorus T.toGrp)
    (hT' : IsSplitTorus T'.toGrp)
    (hb : Function.Injective (RealTorusSpace.cocharacterMapInt t))
    (hindex : Nat.card (cocharacterLattice T' ⧸
      LinearMap.range (RealTorusSpace.cocharacterMapInt t)) = 2) :
    Diagonalizable.homKernelLattice (CommGroupScheme.groupHom t) ≃+ ULift.{u} (ZMod 2) :=
  Classical.choice (nonempty_homKernelLattice_addEquiv t hT hT' hb hindex)

/-- The full scheme-theoretic kernel of the torus map is `μ₂ = D(ℤ/2)`. -/
def torusKernelIso (t : T ⟶ T') (hT : IsSplitTorus T.toGrp)
    (hT' : IsSplitTorus T'.toGrp)
    (hb : Function.Injective (RealTorusSpace.cocharacterMapInt t))
    (hindex : Nat.card (cocharacterLattice T' ⧸
      LinearMap.range (RealTorusSpace.cocharacterMapInt t)) = 2) :
    (Diagonalizable.groupScheme (CommRingCat.of k) (ULift.{u} (ZMod 2))).toGrp ≅
      kernel (CommGroupScheme.groupHom t) :=
  Diagonalizable.congrIso (CommRingCat.of k) (homKernelLatticeEquiv t hT hT' hb hindex).symm ≪≫
    (Diagonalizable.homKernelDiagonalizableIso (CommGroupScheme.groupHom t) hT hT').symm

end TorusKernel

/-! ### Comparison of kernels -/

section Comparison

variable {k : Type u} [Field k]
  {G G' : GroupScheme (Spec (CommRingCat.of k))}
  {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
  {p : G ⟶ G'} {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G'} {t : T ⟶ T'}

/-- A point of the torus kernel maps into the kernel of `p`. -/
theorem comp_comp_eq_one (ht : i ≫ p = CommGroupScheme.groupHom t ≫ i')
    {U : Over (Spec (CommRingCat.of k))} {x : U ⟶ T.X}
    (hx : x ≫ (CommGroupScheme.groupHom t).hom.hom = 1) :
    (x ≫ i.hom.hom) ≫ p.hom.hom = 1 := by
  have hsq : i.hom.hom ≫ p.hom.hom = (CommGroupScheme.groupHom t).hom.hom ≫ i'.hom.hom :=
    congrArg (fun f => f.hom.hom) ht
  rw [Category.assoc, hsq, ← Category.assoc, hx]
  exact MonObj.one_comp _

/-- Postcomposition with `i`, from kernel points of the torus map to kernel points of `p`. -/
def kernelPointsMap (ht : i ≫ p = CommGroupScheme.groupHom t ≫ i')
    (U : Over (Spec (CommRingCat.of k))) :
    ((yonedaGrp.map (CommGroupScheme.groupHom t)).app (op U)).hom.ker →*
      ((yonedaGrp.map p).app (op U)).hom.ker :=
  { toFun := fun x => ⟨(x.val : U ⟶ T.X) ≫ i.hom.hom, comp_comp_eq_one ht x.2⟩
    map_one' := Subtype.ext (MonObj.one_comp _)
    map_mul' := fun _ _ => Subtype.ext (MonObj.mul_comp _ _ _) }

theorem kernelPointsMap_val (ht : i ≫ p = CommGroupScheme.groupHom t ≫ i')
    (U : Over (Spec (CommRingCat.of k)))
    (x : ((yonedaGrp.map (CommGroupScheme.groupHom t)).app (op U)).hom.ker) :
    (kernelPointsMap ht U x).val = x.val ≫ i.hom.hom := rfl

/-- On every test scheme, the kernel of `p` consists exactly of images of torus-kernel points:
kernel points of `p` are central, hence centralize `T`, hence lie in `T` by maximality. -/
theorem kernelPointsMap_bijective (hp : IsCentralIsogeny p) (hG : IsConnectedReductive G)
    (hi : IsMaximalTorus i) (hi' : IsClosedSubgroup i')
    (ht : i ≫ p = CommGroupScheme.groupHom t ≫ i') (U : Over (Spec (CommRingCat.of k))) :
    Function.Bijective (kernelPointsMap ht U) := by
  have : IsClosedImmersion i.hom.hom.left := hi.2.1
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : IsClosedImmersion i'.hom.hom.left := hi'
  have : Mono i'.hom.hom := Over.mono_of_mono_left _
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply (cancel_mono i.hom.hom).1
    exact congrArg Subtype.val hxy
  · intro z
    have hz : z.val ≫ p.hom.hom = 1 := z.2
    have hc : z.val ∈ (torusCentralizer i).carrier U :=
      center_le_torusCentralizer i U (hp.mem_center_of_comp_eq_one hz)
    rw [maximalTorusCentralizer k G hG T i hi] at hc
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.1 hc
    have hsq : i.hom.hom ≫ p.hom.hom = (CommGroupScheme.groupHom t).hom.hom ≫ i'.hom.hom :=
      congrArg (fun f => f.hom.hom) ht
    have hyt : y ≫ (CommGroupScheme.groupHom t).hom.hom = 1 := by
      apply (cancel_mono i'.hom.hom).1
      rw [Category.assoc, ← hsq, ← Category.assoc, hy, hz, MonObj.one_comp]
    exact ⟨⟨y, hyt⟩, Subtype.ext hy⟩

/-- The multiplicative equivalence of kernel points on every test scheme. -/
def kernelPointsComparison (hp : IsCentralIsogeny p) (hG : IsConnectedReductive G)
    (hi : IsMaximalTorus i) (hi' : IsClosedSubgroup i')
    (ht : i ≫ p = CommGroupScheme.groupHom t ≫ i') (U : Over (Spec (CommRingCat.of k))) :
    (U ⟶ (kernel (CommGroupScheme.groupHom t)).X) ≃* (U ⟶ (kernel p).X) :=
  (kernelPointsEquiv (CommGroupScheme.groupHom t) U).trans
    ((MulEquiv.ofBijective (kernelPointsMap ht U)
      (kernelPointsMap_bijective hp hG hi hi' ht U)).trans (kernelPointsEquiv p U).symm)

theorem kernelPointsComparison_comp_kernelι (hp : IsCentralIsogeny p)
    (hG : IsConnectedReductive G) (hi : IsMaximalTorus i) (hi' : IsClosedSubgroup i')
    (ht : i ≫ p = CommGroupScheme.groupHom t ≫ i') (U : Over (Spec (CommRingCat.of k)))
    (x : U ⟶ (kernel (CommGroupScheme.groupHom t)).X) :
    kernelPointsComparison hp hG hi hi' ht U x ≫ (kernelι p).hom.hom =
      x ≫ (kernelι (CommGroupScheme.groupHom t)).hom.hom ≫ i.hom.hom := by
  have h := congrArg Subtype.val ((kernelPointsEquiv p U).apply_symm_apply
    (kernelPointsMap ht U (kernelPointsEquiv (CommGroupScheme.groupHom t) U x)))
  rw [kernelPointsEquiv_val] at h
  rw [← Category.assoc]
  exact h

theorem kernelPointsComparison_naturality (hp : IsCentralIsogeny p)
    (hG : IsConnectedReductive G) (hi : IsMaximalTorus i) (hi' : IsClosedSubgroup i')
    (ht : i ≫ p = CommGroupScheme.groupHom t ≫ i') {U U' : Over (Spec (CommRingCat.of k))}
    (a : U' ⟶ U) (x : U ⟶ (kernel (CommGroupScheme.groupHom t)).X) :
    kernelPointsComparison hp hG hi hi' ht U' (a ≫ x) =
      a ≫ kernelPointsComparison hp hG hi hi' ht U x := by
  apply (cancel_mono (kernelι p).hom.hom).1
  rw [kernelPointsComparison_comp_kernelι, Category.assoc, Category.assoc,
    kernelPointsComparison_comp_kernelι]

/-- The kernel of the torus map is the full kernel of `p`. -/
def kernelComparisonIso (hp : IsCentralIsogeny p) (hG : IsConnectedReductive G)
    (hi : IsMaximalTorus i) (hi' : IsClosedSubgroup i')
    (ht : i ≫ p = CommGroupScheme.groupHom t ≫ i') :
    kernel (CommGroupScheme.groupHom t) ≅ kernel p :=
  isoOfPoints (kernelPointsComparison hp hG hi hi' ht)
    (kernelPointsComparison_naturality hp hG hi hi' ht)

theorem kernelComparisonIso_hom_kernelι (hp : IsCentralIsogeny p)
    (hG : IsConnectedReductive G) (hi : IsMaximalTorus i) (hi' : IsClosedSubgroup i')
    (ht : i ≫ p = CommGroupScheme.groupHom t ≫ i') :
    (kernelComparisonIso hp hG hi hi' ht).hom ≫ kernelι p =
      kernelι (CommGroupScheme.groupHom t) ≫ i := by
  apply hom_ext_points
  intro U x
  rw [Grp.comp_hom_hom, Grp.comp_hom_hom, ← Category.assoc, kernelComparisonIso,
    comp_isoOfPoints_hom, kernelPointsComparison_comp_kernelι]

end Comparison

end IndexTwoKernel

/-! ### The kernel is `μ₂` -/

section Main

variable {k : Type u} [Field k]
  {G G' : GroupScheme (Spec (CommRingCat.of k))}
  {T T' : CommGroupScheme (Spec (CommRingCat.of k))}

/-- **Index two gives kernel `μ₂`.** Let `p : G ⟶ G'` be a central isogeny over a field with `G`
connected reductive, `i : T ⟶ G` a split maximal torus, `i' : T' ⟶ G'` a closed split torus and
`t : T ⟶ T'` with `i ≫ p = t ≫ i'`. If the image of `X_*(T)` in `X_*(T')` has index two, then
the full scheme-theoretic kernel of `p` is isomorphic to `μ₂ = D(ℤ/2)`. -/
def IsCentralIsogeny.indexTwoKernelIso {p : G ⟶ G'} (hp : IsCentralIsogeny p)
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G'} (hi : IsMaximalTorus i)
    (hi' : IsClosedSubgroup i') (t : T ⟶ T')
    (ht : i ≫ p = CommGroupScheme.groupHom t ≫ i')
    (hindex : Nat.card (cocharacterLattice T' ⧸
      LinearMap.range (RealTorusSpace.cocharacterMapInt t)) = 2) :
    (Diagonalizable.groupScheme (CommRingCat.of k) (ULift.{u} (ZMod 2))).toGrp ≅ kernel p :=
  IndexTwoKernel.torusKernelIso t hT hT'
      (hp.cocharacterMapInt_injective_of_square hi.2.1 hi' t ht) hindex ≪≫
    IndexTwoKernel.kernelComparisonIso hp hG hi hi' ht

/-- The isomorphism lands, inside `G`, in the torus: composed with the kernel inclusion of `p`
it is the torus-kernel inclusion followed by `i`. -/
theorem IsCentralIsogeny.indexTwoKernelIso_hom_kernelι {p : G ⟶ G'} (hp : IsCentralIsogeny p)
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G'} (hi : IsMaximalTorus i)
    (hi' : IsClosedSubgroup i') (t : T ⟶ T')
    (ht : i ≫ p = CommGroupScheme.groupHom t ≫ i')
    (hindex : Nat.card (cocharacterLattice T' ⧸
      LinearMap.range (RealTorusSpace.cocharacterMapInt t)) = 2) :
    (hp.indexTwoKernelIso hG hT hT' hi hi' t ht hindex).hom ≫ kernelι p =
      (IndexTwoKernel.torusKernelIso t hT hT'
        (hp.cocharacterMapInt_injective_of_square hi.2.1 hi' t ht) hindex).hom ≫
        kernelι (CommGroupScheme.groupHom t) ≫ i := by
  rw [indexTwoKernelIso, Iso.trans_hom, Category.assoc,
    IndexTwoKernel.kernelComparisonIso_hom_kernelι]

end Main

end Langlands.GroupScheme
