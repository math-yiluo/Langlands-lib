import Langlands.AbelianScheme.Tate.TwoPowerTorsionClosure
import Langlands.AlgebraicGeometry.LocallyNoetherianConnectedComponentOpenProof
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Logic.Function.Iterate

/-! # Closure of actual prime-power torsion -/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry TopologicalSpace
open scoped CategoryTheory.MonObj

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.Tate.PrimePowerTorsion

universe u

section Locus

variable {K : Type u} [Field K]
  (A : AbelianScheme (Spec (CommRingCat.of K))) (p : ℕ)

/-- Underlying points of actual geometric sections killed by some power of p. -/
def locus : Set A.X.left :=
  {x | ∃ (n : ℕ) (s : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X),
    s ^ (p ^ n) = 1 ∧ s.left (default : Spec (CommRingCat.of K)) = x}

lemma pow_prime_section_apply
    (s : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X) :
    (s ^ (p : ℕ)).left (default : Spec (CommRingCat.of K)) =
      (GroupScheme.multiplication A.toGrp (p : ℤ)).hom.hom.left
        (s.left (default : Spec (CommRingCat.of K))) := by
  have h : s ≫ (GroupScheme.multiplication A.toGrp (p : ℤ)).hom.hom = s ^ (p : ℕ) := by
    simpa only [zpow_natCast] using!
      (GroupScheme.points_multiplication A.toGrp (p : ℤ) _ s)
  rw [← h, Over.comp_left, Scheme.Hom.comp_apply]

/-- Multiplication by p preserves the actual torsion locus. -/
theorem multiplication_prime_mapsTo_locus :
    Set.MapsTo (GroupScheme.multiplication A.toGrp (p : ℤ)).hom.hom.left
      (locus A p) (locus A p) := by
  rintro x ⟨n, s, hs, rfl⟩
  refine ⟨n, s ^ (p : ℕ), ?_, pow_prime_section_apply A p s⟩
  rw [← pow_mul, Nat.mul_comm p (p ^ n), pow_mul, hs, one_pow]

variable [IsAlgClosed K]

/-- Inverse images of actual prime-power torsion lie in its closure. The argument
uses density of closed points in each actual fibre. -/
theorem preimage_locus_subset_closure :
    (GroupScheme.multiplication A.toGrp (p : ℤ)).hom.hom.left ⁻¹'
      locus A p ⊆ closure (locus A p) := by
  let f := (GroupScheme.multiplication A.toGrp (p : ℤ)).hom.hom
  have : JacobsonSpace A.X.left := LocallyOfFiniteType.jacobsonSpace A.X.hom
  rintro x ⟨n, s, hs, hsx⟩
  let F : Set A.X.left := f.left ⁻¹'
    {s.left (default : Spec (CommRingCat.of K))}
  have hF : IsClosed F := (isClosed_point_of_section A s).preimage f.left.continuous
  have hsub : F ∩ closedPoints A.X.left ⊆ locus A p := by
    rintro y ⟨hy, hyc⟩
    let t : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X :=
      Over.homMk (pointOfClosedPoint A.X.hom y hyc)
        (pointOfClosedPoint_comp A.X.hom y hyc)
    have hty : t.left (default : Spec (CommRingCat.of K)) = y :=
      pointOfClosedPoint_apply A.X.hom y hyc _
    have ht : t ^ (p : ℕ) = s := by
      apply Over.OverMorphism.ext
      apply ext_of_apply_closedPoint_eq A.X.hom (t ^ (p : ℕ)).w s.w
      have he := pow_prime_section_apply A p t
      rw [hty] at he
      simpa only [Subsingleton.elim (IsLocalRing.closedPoint K)
        (default : Spec (CommRingCat.of K))] using! he.trans hy
    refine ⟨n + 1, t, ?_, ?_⟩
    · rw [pow_succ, Nat.mul_comm (p ^ n) p, pow_mul, ht, hs]
    · exact hty
  have hclosure : closure (F ∩ closedPoints A.X.left) = F := by
    rw [JacobsonSpace.closure_inter_closedPoints_eq_closure hF.isLocallyClosed,
      hF.closure_eq]
  apply closure_mono hsub
  rw [hclosure]
  exact hsx.symm

variable [CharZero K] [Fact p.Prime]

/-- Multiplication by p maps the actual torsion locus onto itself. -/
theorem image_locus_multiplication_prime :
    (GroupScheme.multiplication A.toGrp (p : ℤ)).hom.hom.left ''
      locus A p = locus A p := by
  apply Set.Subset.antisymm
  · exact Set.image_subset_iff.mpr (multiplication_prime_mapsTo_locus A p)
  · rintro x ⟨n, s, hs, hsx⟩
    obtain ⟨t, ht⟩ := algClosedPointDivisibility _ A K (𝟙 _) p
      (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) s
    refine ⟨t.left (default : Spec (CommRingCat.of K)), ⟨n + 1, t, ?_, rfl⟩, ?_⟩
    · rw [pow_succ, Nat.mul_comm (p ^ n) p, pow_mul, ht, hs]
    · rw [← pow_prime_section_apply A p t, ht, hsx]

/-- The actual Zariski closure is stable under full inverse image by
multiplication by p. -/
theorem preimage_closure_locus_multiplication_prime :
    (GroupScheme.multiplication A.toGrp (p : ℤ)).hom.hom.left ⁻¹'
      closure (locus A p) = closure (locus A p) := by
  let f := (GroupScheme.multiplication A.toGrp (p : ℤ)).hom.hom.left
  have : Etale f := multiplication_etale_of_field A p (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  rw [f.isOpenMap.preimage_closure_eq_closure_preimage f.continuous]
  apply Set.Subset.antisymm
  · exact (closure_mono (preimage_locus_subset_closure A p)).trans_eq
      closure_closure
  · exact closure_mono (multiplication_prime_mapsTo_locus A p)

/-- The actual Zariski closure maps onto itself under multiplication by p. -/
theorem image_closure_locus_multiplication_prime :
    (GroupScheme.multiplication A.toGrp (p : ℤ)).hom.hom.left ''
      closure (locus A p) = closure (locus A p) := by
  let f := (GroupScheme.multiplication A.toGrp (p : ℤ)).hom.hom.left
  have : IsFinite f := multiplication_isFinite_of_ne_zero A p (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  rw [← f.isClosedMap.closure_image_eq_of_continuous f.continuous,
    image_locus_multiplication_prime]



end Locus

section Connectedness

variable {K : Type u} [Field K]
  (A : AbelianScheme (Spec (CommRingCat.of K))) (p : ℕ)

private theorem connectedSpace_of_dense_eventually_fixed
    {X : Type*} [TopologicalSpace X] [NoetherianSpace X]
    (f : X → X) (hf : Continuous f) (hsurj : Function.Surjective f)
    (e : X) (he : f e = e) (T : Set X) (hT : Dense T)
    (hkill : ∀ x ∈ T, ∃ n : ℕ, f^[n] x = e) : ConnectedSpace X := by
  classical
  let : DiscreteTopology (ConnectedComponents X) :=
    ConnectedComponents.discreteTopology_iff.mpr fun x =>
      Langlands.AlgebraicGeometry.isOpen_connectedComponent_of_noetherianSpace x
  let : Finite (ConnectedComponents X) := finite_of_compact_of_discrete
  let g := hf.connectedComponentsMap
  have hginj : Function.Injective g :=
    Finite.injective_iff_surjective.mpr (hf.connectedComponentsMap_surjective hsurj)
  have hiter (n : ℕ) (x : X) :
      g^[n] (ConnectedComponents.mk x) = ConnectedComponents.mk (f^[n] x) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      exact hf.connectedComponentsMap_mk _
  have hfixed (n : ℕ) : f^[n] e = e := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih, he]
  have hsub : T ⊆ connectedComponent e := by
    intro x hx
    obtain ⟨n, hn⟩ := hkill x hx
    apply ConnectedComponents.coe_eq_coe'.mp
    apply hginj.iterate n
    rw [hiter, hiter, hn, hfixed]
  apply connectedSpace_iff_connectedComponent.mpr
  refine ⟨e, Set.eq_univ_of_forall fun x => ?_⟩
  exact (closure_minimal hsub isClosed_connectedComponent) (hT x)

/-- Iterating actual multiplication by p on a section evaluates its
`p^n`-th power. -/
theorem multiplication_prime_iterate_section (n : ℕ)
    (s : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X) :
    ((GroupScheme.multiplication A.toGrp (p : ℤ)).hom.hom.left : A.X.left → A.X.left)^[n]
      (s.left (default : Spec (CommRingCat.of K))) =
        (s ^ (p ^ n)).left (default : Spec (CommRingCat.of K)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, ← pow_prime_section_apply, ← pow_mul, ← pow_succ]

variable [IsAlgClosed K] [CharZero K] [Fact p.Prime]

/-- The actual Zariski closure of geometric prime-power torsion is connected. -/
theorem isConnected_closure_locus :
    _root_.IsConnected (closure (locus A p)) := by
  have : CompactSpace A.X.left := QuasiCompact.compactSpace_of_compactSpace A.X.hom
  have : IsLocallyNoetherian A.X.left := LocallyOfFiniteType.isLocallyNoetherian A.X.hom
  have : IsNoetherian A.X.left := {}
  let T := locus A p
  let C := closure T
  let f : A.X.left → A.X.left :=
    (GroupScheme.multiplication A.toGrp (p : ℤ)).hom.hom.left
  have hf : Continuous f :=
    (GroupScheme.multiplication A.toGrp (p : ℤ)).hom.hom.left.continuous
  have himage : f '' C = C := image_closure_locus_multiplication_prime A p
  have hmap : Set.MapsTo f C C := by
    intro x hx
    rw [← himage]
    exact Set.mem_image_of_mem f hx
  let F : C → C := fun x => ⟨f x.1, hmap x.2⟩
  have hF : Continuous F := (hf.comp continuous_subtype_val).subtype_mk _
  have hFsurj : Function.Surjective F := by
    intro x
    have hx : x.1 ∈ f '' C := by rw [himage]; exact x.2
    obtain ⟨y, hy, hxy⟩ := hx
    exact ⟨⟨y, hy⟩, Subtype.ext hxy⟩
  let s : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X := 1
  let e := s.left (default : Spec (CommRingCat.of K))
  have heT : e ∈ T := ⟨0, s, by simp [s], rfl⟩
  let E : C := ⟨e, subset_closure heT⟩
  have hFE : F E = E := by
    apply Subtype.ext
    change f e = e
    dsimp only [f, e]
    rw [← pow_prime_section_apply A p s]
    simp [s]
  have hiter (n : ℕ) (x : C) : (F^[n] x).1 = f^[n] x.1 := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
  have hTdense : Dense (Subtype.val ⁻¹' T : Set C) := by
    apply Subtype.dense_iff.mpr
    have himg : Subtype.val '' (Subtype.val ⁻¹' T : Set C) = T := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, subset_closure hx⟩, hx, rfl⟩
    rw [himg]
  have : ConnectedSpace C :=
    connectedSpace_of_dense_eventually_fixed F hF hFsurj E hFE _ hTdense (by
      rintro x ⟨n, t, ht, htx⟩
      refine ⟨n, Subtype.ext ?_⟩
      rw [hiter, ← htx, multiplication_prime_iterate_section, ht])
  exact isConnected_iff_connectedSpace.mpr this



end Connectedness

section Subgroup

variable {K : Type u} [Field K]
  (A : AbelianScheme (Spec (CommRingCat.of K))) (p : ℕ)

private lemma comp_mulRight (s t : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X) :
    s ≫ (GrpObj.mulRight t).hom = s * t := by
  change s ≫ ((𝟙 A.X) * (toUnit A.X ≫ t)) = s * t
  rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc]
  have h : s ≫ toUnit A.X = 𝟙 _ := toUnit_unique _ _
  rw [h, Category.id_comp]

private lemma mulRight_apply_section
    (s t : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X) :
    (GrpObj.mulRight t).hom.left (s.left (default : Spec (CommRingCat.of K))) =
      (s * t).left (default : Spec (CommRingCat.of K)) := by
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, comp_mulRight]

private lemma section_torsion_one :
    (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X).left
      (default : Spec (CommRingCat.of K)) ∈ locus A p := by
  exact ⟨0, 1, by simp, rfl⟩

private lemma torsion_pow_mul
    (s t : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X)
    (n m : ℕ) (hs : s ^ (p ^ n) = 1) (ht : t ^ (p ^ m) = 1) :
    (s * t) ^ (p ^ (n + m)) = 1 := by
  rw [mul_pow]
  have hs' : s ^ (p ^ (n + m)) = 1 := by
    rw [pow_add, pow_mul, hs, one_pow]
  have ht' : t ^ (p ^ (n + m)) = 1 := by
    rw [Nat.add_comm, pow_add, pow_mul, ht, one_pow]
  rw [hs', ht', one_mul]

private lemma inv_mapsTo_locus :
    Set.MapsTo (ι[A.X].left) (locus A p) (locus A p) := by
  rintro x ⟨n, s, hs, rfl⟩
  refine ⟨n, s⁻¹, by simp [inv_pow, hs], ?_⟩
  rw [Hom.inv_def, Over.comp_left, Scheme.Hom.comp_apply]

private lemma inv_mapsTo_closure :
    Set.MapsTo (ι[A.X].left) (closure (locus A p))
      (closure (locus A p)) :=
  (inv_mapsTo_locus A p).closure (ι[A.X].left.continuous)

private lemma torsion_mulRight_mapsTo_closure
    (t : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X)
    (m : ℕ) (ht : t ^ (p ^ m) = 1) :
    Set.MapsTo (GrpObj.mulRight t).hom.left (closure (locus A p))
      (closure (locus A p)) := by
  apply Set.MapsTo.closure _ (GrpObj.mulRight t).hom.left.continuous
  rintro x ⟨n, s, hs, rfl⟩
  exact ⟨n + m, s * t, torsion_pow_mul A p s t n m hs ht,
    (mulRight_apply_section A s t).symm⟩

private lemma mulRight_mapsTo_closure
    (s : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X)
    (hs : s.left (default : Spec (CommRingCat.of K)) ∈ closure (locus A p)) :
    Set.MapsTo (GrpObj.mulRight s).hom.left (closure (locus A p))
      (closure (locus A p)) := by
  apply Set.MapsTo.closure_left _ (GrpObj.mulRight s).hom.left.continuous isClosed_closure
  rintro x ⟨n, t, ht, rfl⟩
  rw [mulRight_apply_section, mul_comm, ← mulRight_apply_section]
  exact torsion_mulRight_mapsTo_closure A p t n ht hs

/-- The actual sections landing in the Zariski closure form a subgroup. -/
def closureSectionSubgroup :
    Subgroup (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X) where
  carrier := {s | s.left (default : Spec (CommRingCat.of K)) ∈ closure (locus A p)}
  one_mem' := subset_closure (section_torsion_one A p)
  mul_mem' := by
    intro s t hs ht
    change (s * t).left (default : Spec (CommRingCat.of K)) ∈
      closure (locus A p)
    rw [← mulRight_apply_section]
    exact mulRight_mapsTo_closure A p t ht hs
  inv_mem' := by
    intro s hs
    change (s⁻¹).left (default : Spec (CommRingCat.of K)) ∈
      closure (locus A p)
    rw [Hom.inv_def]
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    exact inv_mapsTo_closure A p hs

/-- Translation by any section in the closure preserves the entire closure. -/
theorem image_closure_mulRight
    (s : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X)
    (hs : s.left (default : Spec (CommRingCat.of K)) ∈ closure (locus A p)) :
    (GrpObj.mulRight s).hom.left '' closure (locus A p) =
      closure (locus A p) := by
  apply Set.Subset.antisymm (mulRight_mapsTo_closure A p s hs).image_subset
  intro x hx
  have hsinv : s⁻¹ ∈ closureSectionSubgroup A p :=
    (closureSectionSubgroup A p).inv_mem hs
  refine ⟨(GrpObj.mulRight s⁻¹).hom.left x, mulRight_mapsTo_closure A p s⁻¹ hsinv hx, ?_⟩
  have hcomp : (GrpObj.mulRight s⁻¹).hom ≫ (GrpObj.mulRight s).hom = 𝟙 A.X := by
    change ((𝟙 A.X) * (toUnit A.X ≫ s⁻¹)) ≫
      ((𝟙 A.X) * (toUnit A.X ≫ s)) = 𝟙 A.X
    rw [MonObj.comp_mul]
    simp [GrpObj.comp_inv]
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hcomp]
  rfl



end Subgroup

end Langlands.AbelianScheme.Tate.PrimePowerTorsion
