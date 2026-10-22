import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic

/-!
# A comparison chain map from the finite cyclic resolution to the bar resolution
-/

open CategoryTheory Finsupp

namespace Langlands.Cohomology.CyclicH2

universe u

variable (k : Type u) {G : Type u} [CommRing k] [CommGroup G] [Fintype G]

omit [Fintype G] in
lemma leftRegular_hom_ext {A : Rep k G} {f f' : Rep.leftRegular k G ⟶ A}
    (h : f.hom (MonoidAlgebra.single 1 1) = f'.hom (MonoidAlgebra.single 1 1)) : f = f' :=
  (Rep.leftRegularHomEquiv A).injective h

namespace CyclicToBar

/-- Degree zero: `1 ↦ []`. -/
noncomputable abbrev f₀ : Rep.leftRegular k G ⟶ Rep.free k G (Fin 0 → G) :=
  Rep.leftRegularHom _ (Finsupp.single ![] (MonoidAlgebra.single 1 1))

/-- Degree one: `1 ↦ [g]`. -/
noncomputable abbrev f₁ (g : G) : Rep.leftRegular k G ⟶ Rep.free k G (Fin 1 → G) :=
  Rep.leftRegularHom _ (Finsupp.single ![g] (MonoidAlgebra.single 1 1))

/-- Degree two: `1 ↦ ∑ i < |G|, [g ^ i | g]`. -/
noncomputable abbrev f₂ (g : G) : Rep.leftRegular k G ⟶ Rep.free k G (Fin 2 → G) :=
  Rep.leftRegularHom _
    (∑ i ∈ Finset.range (Fintype.card G), Finsupp.single ![g ^ i, g] (MonoidAlgebra.single 1 1))

omit [Fintype G] in
lemma contractNth_zero_pair (a b : G) :
    Fin.contractNth (0 : Fin 2) (· * ·) ![a, b] = ![a * b] := by
  funext j; fin_cases j; rfl

omit [Fintype G] in
lemma contractNth_one_pair (a b : G) :
    Fin.contractNth (1 : Fin 2) (· * ·) ![a, b] = ![a] := by
  funext j; fin_cases j; rfl

omit [CommGroup G] [Fintype G] in
lemma tail_pair (a b : G) : (fun j : Fin 1 => ![a, b] j.succ) = ![b] := by
  funext j; fin_cases j; rfl

lemma sum_range_card_pow {M : Type*} [AddCommMonoid M] (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (F : G → M) :
    ∑ i ∈ Finset.range (Fintype.card G), F (g ^ i) = ∑ h, F h := by
  classical
  rw [← Nat.card_eq_fintype_card, ← orderOf_eq_card_of_forall_mem_zpowers hg]
  refine Finset.sum_nbij (g ^ ·) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
  · rw [Finset.coe_range]
    exact pow_injOn_Iio_orderOf
  · intro h _
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 (mem_zpowers_iff_mem_range_orderOf.1 (hg h))
    exact ⟨i, hi, rfl⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma resolution_d_one_zero (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    (Rep.FiniteCyclicGroup.resolution k g hg).complex.d 1 0 =
      Rep.applyAsHom (Rep.leftRegular k G) g - 𝟙 _ := by
  simp [HomologicalComplex.alternatingConst]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma resolution_d_two_one (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    (Rep.FiniteCyclicGroup.resolution k g hg).complex.d 2 1 = (Rep.leftRegular k G).norm := by
  simp [HomologicalComplex.alternatingConst]

omit [Fintype G] in
lemma f₀_apply (h : G) (r : k) :
    (f₀ k (G := G)).hom (MonoidAlgebra.single h r) = single ![] (MonoidAlgebra.single h r) := by
  rw [Rep.leftRegularHom_hom_single]
  simp

omit [Fintype G] in
lemma f₁_apply (g h : G) (r : k) :
    (f₁ k g).hom (MonoidAlgebra.single h r) = single ![g] (MonoidAlgebra.single h r) := by
  rw [Rep.leftRegularHom_hom_single]
  simp

lemma f₂_one (g : G) :
    (f₂ k g).hom (MonoidAlgebra.single 1 1) = ∑ i ∈ Finset.range (Fintype.card G),
      single ![g ^ i, g] (MonoidAlgebra.single 1 1) := by
  rw [Rep.leftRegularHom_hom_single]
  simp

omit [Fintype G] in
lemma applyAsHom_single (g h : G) (r : k) :
    ((Rep.leftRegular k G).applyAsHom g).hom (MonoidAlgebra.single h r) =
      MonoidAlgebra.single (g * h) r := by
  rw [Rep.applyAsHom_apply]
  simp [Representation.ofMulAction_single]

lemma norm_single_one :
    (Rep.leftRegular k G).norm.hom (MonoidAlgebra.single 1 1) =
      ∑ h : G, MonoidAlgebra.single h (1 : k) := by
  rw [Rep.norm_apply]
  simp [Representation.norm, Representation.ofMulAction_single]

omit [Fintype G] in
lemma comm₁_aux (g : G) :
    f₁ k g ≫ Rep.barComplex.d k G 0 = (Rep.applyAsHom (Rep.leftRegular k G) g - 𝟙 _) ≫ f₀ k := by
  apply leftRegular_hom_ext
  simp only [Rep.hom_comp, Representation.IntertwiningMap.comp_apply]
  rw [f₁_apply, Rep.barComplex.d_single]
  simp only [Rep.sub_hom, Rep.hom_id, Representation.IntertwiningMap.coe_sub, Pi.sub_apply,
    Representation.IntertwiningMap.id_apply, map_sub]
  rw [applyAsHom_single, f₀_apply, f₀_apply, Fin.sum_univ_one]
  have e : ∀ x y : Fin 0 → G, x = y := fun _ _ => Subsingleton.elim _ _
  rw [e (fun i => ![g] i.succ) ![], e (Fin.contractNth _ _ _) ![]]
  simp [sub_eq_add_neg, MonoidAlgebra.single_neg]

omit [Fintype G] in
lemma d_single_pair (g : G) (i : ℕ) :
    (Rep.barComplex.d k G 1).hom (single ![g ^ i, g] (MonoidAlgebra.single 1 1)) =
      single ![g] (MonoidAlgebra.single (g ^ i) 1) +
        (single ![g ^ i] (MonoidAlgebra.single 1 1) -
          single ![g ^ (i + 1)] (MonoidAlgebra.single 1 1)) := by
  rw [Rep.barComplex.d_single, Fin.sum_univ_two, contractNth_zero_pair, contractNth_one_pair,
    tail_pair]
  simp [pow_succ, sub_eq_add_neg, MonoidAlgebra.single_neg, add_comm]

lemma comm₂_aux (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    f₂ k g ≫ Rep.barComplex.d k G 1 = (Rep.leftRegular k G).norm ≫ f₁ k g := by
  apply leftRegular_hom_ext
  simp only [Rep.hom_comp, Representation.IntertwiningMap.comp_apply]
  rw [f₂_one, map_sum, norm_single_one, map_sum]
  rw [Finset.sum_congr rfl (fun i _ => d_single_pair k g i), Finset.sum_add_distrib,
    Finset.sum_range_sub' (fun i => single ![g ^ i] (MonoidAlgebra.single (1 : G) (1 : k))),
    pow_card_eq_one, pow_zero, sub_self, add_zero,
    sum_range_card_pow g hg (fun h => single ![g] (MonoidAlgebra.single h (1 : k)))]
  exact Finset.sum_congr rfl (fun h _ => (f₁_apply k g h 1).symm)

lemma comm₁ (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    f₁ k g ≫ (Rep.barComplex k G).d 1 0 =
      (Rep.FiniteCyclicGroup.resolution k g hg).complex.d 1 0 ≫ f₀ k := by
  rw [resolution_d_one_zero, Rep.barComplex.d_def]
  exact comm₁_aux k g

lemma comm₂ (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    f₂ k g ≫ (Rep.barComplex k G).d 2 1 =
      (Rep.FiniteCyclicGroup.resolution k g hg).complex.d 2 1 ≫ f₁ k g := by
  rw [resolution_d_two_one, Rep.barComplex.d_def]
  exact comm₂_aux k g hg

end CyclicToBar

variable (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)

open CyclicToBar in
/-- An explicit chain map from Mathlib's finite cyclic resolution to the bar resolution. -/
noncomputable def cyclicToBar :
    (Rep.FiniteCyclicGroup.resolution k g hg).complex ⟶ Rep.barComplex k G := by
  classical
  exact ChainComplex.mkHom _ _ (f₀ k) (f₁ k g) (comm₁ k g hg)
    (fun n p => match n, p with
      | 0, p => if h : p.2.1 = f₁ k g then ⟨f₂ k g, by rw [h]; exact comm₂ k g hg⟩ else
          ProjectiveResolution.liftFSucc (Rep.FiniteCyclicGroup.resolution k g hg)
            (Rep.barResolution k G) 0 p.1 p.2.1 p.2.2
      | n + 1, p => ProjectiveResolution.liftFSucc (Rep.FiniteCyclicGroup.resolution k g hg)
            (Rep.barResolution k G) (n + 1) p.1 p.2.1 p.2.2)

lemma cyclicToBar_f_zero : (cyclicToBar k g hg).f 0 = CyclicToBar.f₀ k := rfl

lemma cyclicToBar_f_two : (cyclicToBar k g hg).f 2 = CyclicToBar.f₂ k g :=
  (ChainComplex.mkHom_f_succ_succ _ _ _ _ _ _ 0).trans (congrArg PSigma.fst (dite_eq_left rfl))

/-- The degree-two component sends `1` to `∑ i < |G|, [g ^ i | g]`. -/
lemma cyclicToBar_f_two_single :
    ((cyclicToBar k g hg).f 2).hom (MonoidAlgebra.single 1 1) =
      ∑ i ∈ Finset.range (Fintype.card G),
        Finsupp.single ![g ^ i, g] (MonoidAlgebra.single 1 1) := by
  rw [cyclicToBar_f_two]
  exact CyclicToBar.f₂_one k g

omit [Fintype G] in
lemma barResolution_π_f_zero :
    (Rep.barResolution k G).π.f 0 =
      (Rep.diagonalSuccIsoFree k G 0).inv ≫ Rep.standardComplex.ε k G := rfl

lemma resolution_π_f_zero :
    (Rep.FiniteCyclicGroup.resolution k g hg).π.f 0 =
      Rep.leftRegularHom (Rep.trivial k G k) 1 :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

omit [Fintype G] in
lemma diagonalSuccIsoFree_inv_single (m : ℕ) (f : Fin m → G) (h : G) (r : k) :
    (Rep.diagonalSuccIsoFree k G m).inv.hom (single f (MonoidAlgebra.single h r)) =
      MonoidAlgebra.single (h • Fin.partialProd f) r := by
  simp only [Rep.diagonalSuccIsoFree, Rep.diagonalSuccIsoTensorTrivial, Iso.trans_inv,
    Rep.hom_comp, Representation.IntertwiningMap.comp_apply]
  have step1 : (Rep.Hom.hom (Rep.leftRegularTensorTrivialIsoFree k G (Fin m → G)).inv)
      (single f (.single h r)) = .single h 1 ⊗ₜ[k] .single f r :=
    Representation.leftRegularTensorTrivialIsoFree_symm_apply_single_single f h r
  rw [step1]
  have key₁ := Representation.linearizeMap_single (k := k)
    (Action.diagonalSuccIsoTensorTrivial G m).inv (h, f) ((1 : k) * r)
  have key₂ := Representation.LinearizeMonoidal.μ_apply_single_single (k := k)
    (X := Action.leftRegular G) (Y := Action.trivial G (Fin m → G)) h f 1 r
  refine ((congrArg (fun z => (Representation.linearizeMap
    (Action.diagonalSuccIsoTensorTrivial G m).inv) z) key₂).trans key₁).trans ?_
  rw [one_mul]
  congr 1
  exact Action.diagonalSuccIsoTensorTrivial_inv_hom_apply h f

omit [Fintype G] in
lemma f₀_comp_ε :
    CyclicToBar.f₀ k ≫ (Rep.diagonalSuccIsoFree k G 0).inv ≫ Rep.standardComplex.ε k G =
      Rep.leftRegularHom (Rep.trivial k G k) 1 := by
  apply leftRegular_hom_ext
  simp only [Rep.hom_comp, Representation.IntertwiningMap.comp_apply]
  rw [CyclicToBar.f₀_apply, diagonalSuccIsoFree_inv_single, Rep.leftRegularHom_hom_single]
  simp [Rep.standardComplex.ε]

/-- The degree-zero component is compatible with the two augmentations to `k`. -/
lemma cyclicToBar_f_zero_comp_π :
    (cyclicToBar k g hg).f 0 ≫ (Rep.barResolution k G).π.f 0 =
      (Rep.FiniteCyclicGroup.resolution k g hg).π.f 0 :=
  (f₀_comp_ε k).trans (resolution_π_f_zero k g hg).symm

end Langlands.Cohomology.CyclicH2
