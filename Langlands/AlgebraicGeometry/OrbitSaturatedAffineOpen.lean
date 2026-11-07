import Langlands.AlgebraicGeometry.PointTopology.FiniteAffineNeighborhoodsOpenShrinking
import Langlands.AlgebraicGeometry.GenericPointAvoidance
import Mathlib.AlgebraicGeometry.QuasiAffine

/-! # Saturated affine opens from finite group orbits -/

noncomputable section

universe u

open CategoryTheory TopologicalSpace Opposite
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.OrbitSaturatedAffineOpen

section Avoidance

/-- Davis prime avoidance: a coset `x + I` avoids finitely many primes not containing `I`. -/
theorem exists_add_notMem_of_not_le {A : Type*} [CommRing A] (I : Ideal A) (x : A)
    (s : Finset (Ideal A)) (hp : ∀ p ∈ s, p.IsPrime) (hI : ∀ p ∈ s, ¬ I ≤ p) :
    ∃ e ∈ I, ∀ p ∈ s, x + e ∉ p := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact ⟨0, I.zero_mem, by simp⟩
  obtain ⟨q, hqs, hmin⟩ := s.exists_minimal hs
  obtain ⟨e', he'I, he'⟩ := ih (s.erase q) (Finset.erase_ssubset hqs)
    (fun p hp' => hp p (Finset.mem_of_mem_erase hp'))
    (fun p hp' => hI p (Finset.mem_of_mem_erase hp'))
  by_cases hxq : x + e' ∈ q
  · have hnle : ¬ I * ∏ p ∈ s.erase q, p ≤ q := by
      intro h
      rcases (hp q hqs).mul_le.mp h with h | h
      · exact hI q hqs h
      · obtain ⟨p, hp', hpq⟩ := (hp q hqs).prod_le.mp h
        have hqp : q ≤ p := hmin (Finset.mem_of_mem_erase hp') hpq
        exact (Finset.mem_erase.mp hp').1 (le_antisymm hpq hqp)
    obtain ⟨y, hy, hyq⟩ := SetLike.not_le_iff_exists.mp hnle
    have hyI : y ∈ I := Ideal.mul_le_left hy
    have hyP : y ∈ ∏ p ∈ s.erase q, p := Ideal.mul_le_right hy
    refine ⟨e' + y, I.add_mem he'I hyI, fun p hp' h => ?_⟩
    by_cases hpq : p = q
    · subst hpq
      apply hyq
      have e : x + (e' + y) - (x + e') = y := by abel
      exact e ▸ p.sub_mem h hxq
    · have hyp : y ∈ p :=
        (Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_erase.mpr ⟨hpq, hp'⟩))) hyP
      apply he' p (Finset.mem_erase.mpr ⟨hpq, hp'⟩)
      have e : x + (e' + y) - y = x + e' := by abel
      exact e ▸ p.sub_mem h hyp
  · refine ⟨e', he'I, fun p hp' => ?_⟩
    by_cases hpq : p = q
    · exact hpq ▸ hxq
    · exact he' p (Finset.mem_erase.mpr ⟨hpq, hp'⟩)

/-- Davis prime avoidance for a finite family of primes indexed by a set. -/
theorem exists_add_notMem_of_finite {A : Type*} [CommRing A] {ι : Type*} (I : Ideal A) (x : A)
    {t : Set ι} (ht : t.Finite) (p : ι → Ideal A) (hp : ∀ i ∈ t, (p i).IsPrime)
    (hI : ∀ i ∈ t, ¬ I ≤ p i) : ∃ e ∈ I, ∀ i ∈ t, x + e ∉ p i := by
  classical
  obtain ⟨e, heI, he⟩ := exists_add_notMem_of_not_le I x (ht.toFinset.image p)
    (by simpa using hp) (by simpa using hI)
  exact ⟨e, heI, fun i hi => he _ (Finset.mem_image_of_mem _ (ht.mem_toFinset.mpr hi))⟩

end Avoidance

section Points

variable {X : Scheme.{u}}

/-- In an affine open, a finite subset of a smaller open lies in a basic open inside it. -/
theorem exists_basicOpen_of_isAffineOpen {U : X.Opens} (hU : IsAffineOpen U)
    {E : Set X} (hE : E.Finite) {V : X.Opens} (hEV : E ⊆ V) (hVU : V ≤ U) :
    ∃ f : Γ(X, U), E ⊆ X.basicOpen f ∧ X.basicOpen f ≤ V := by
  have hinj : Function.Injective hU.fromSpec := hU.fromSpec.isOpenEmbedding.injective
  obtain ⟨f, hfE, hfZ⟩ := GenericPointAvoidance.PrimeSpectrum.exists_basicOpen_of_finite
    (A := Γ(X, U)) (E := hU.fromSpec ⁻¹' E) (hE.preimage hinj.injOn)
    (Z := (((hU.fromSpec ⁻¹ᵁ V : (Spec Γ(X, U)).Opens) : Set (Spec Γ(X, U))))ᶜ)
    (hU.fromSpec ⁻¹ᵁ V).isOpen.isClosed_compl
    (Set.disjoint_compl_right_iff_subset.mpr fun y hy => hEV hy)
  refine ⟨f, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨y, rfl⟩ : x ∈ Set.range hU.fromSpec := by
      rw [hU.range_fromSpec]; exact hVU (hEV hx)
    have : y ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen f := by
      rw [hU.fromSpec_preimage_basicOpen]; exact hfE hx
    exact this
  · obtain ⟨y, rfl⟩ : x ∈ Set.range hU.fromSpec := by
      rw [hU.range_fromSpec]; exact X.basicOpen_le f hx
    have hy : y ∈ PrimeSpectrum.basicOpen f := by
      rw [← hU.fromSpec_preimage_basicOpen]; exact hx
    by_contra hxV
    exact Set.disjoint_left.mp hfZ hy hxV

/-- A finite subset of a quasi-affine scheme lies in an affine basic open of a global section. -/
theorem exists_basicOpen_isAffineOpen_of_finite (X : Scheme.{u}) [X.IsQuasiAffine] {E : Set X}
    (hE : E.Finite) : ∃ s : Γ(X, ⊤), E ⊆ X.basicOpen s ∧ IsAffineOpen (X.basicOpen s) := by
  obtain ⟨a, haE, ha⟩ := GenericPointAvoidance.exists_basicOpen_of_finite
    (hE.image X.toSpecΓ) (W := X.toSpecΓ.opensRange)
    (by rintro _ ⟨x, _, rfl⟩; exact ⟨x, rfl⟩)
  refine ⟨X.toSpecΓ.appTop a, fun x hx => ?_, ?_⟩
  · rw [← Scheme.preimage_basicOpen_top]
    exact haE ⟨x, hx, rfl⟩
  · rw [← Scheme.preimage_basicOpen_top]
    exact ((isAffineOpen_top _).basicOpen a).preimage_of_isOpenImmersion X.toSpecΓ ha

/-- The prime ideal of sections over `U` vanishing at a point of `U`. -/
def pointIdeal {U : X.Opens} (x : X) (hx : x ∈ U) : Ideal Γ(X, U) :=
  RingHom.ker (X.evaluation U x hx).hom

theorem mem_pointIdeal {U : X.Opens} (x : X) (hx : x ∈ U) (f : Γ(X, U)) :
    f ∈ pointIdeal x hx ↔ x ∉ X.basicOpen f := by
  simp [pointIdeal, RingHom.mem_ker]

instance {U : X.Opens} (x : X) (hx : x ∈ U) : (pointIdeal x hx).IsPrime :=
  RingHom.ker_isPrime _

end Points

section Norm

variable {X : Scheme.{u}}

theorem mem_basicOpen_prod {U : X.Opens} {ι : Type*} (s : Finset ι) (f : ι → Γ(X, U))
    (x : X) : x ∈ X.basicOpen (∏ i ∈ s, f i) ↔ x ∈ U ∧ ∀ i ∈ s, x ∈ X.basicOpen (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [Scheme.basicOpen_of_isUnit (X := X) isUnit_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Scheme.basicOpen_mul]
    simp only [Opens.mem_inf, ih, Finset.mem_insert, forall_eq_or_imp]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h2, h1, h3⟩
    · rintro ⟨h2, h1, h3⟩
      exact ⟨h1, h2, h3⟩

variable {G : Type*} [Group G] [Fintype G] (σ : G → (X ⟶ X))

/-- The norm of a global function along a finite family of endomorphisms. -/
def norm (r : Γ(X, ⊤)) : Γ(X, ⊤) := ∏ g, (σ g).appTop r

theorem appTop_norm (hσ : ∀ g h, σ g ≫ σ h = σ (g * h)) (h : G) (r : Γ(X, ⊤)) :
    (σ h).appTop (norm σ r) = norm σ r := by
  simp only [norm, map_prod]
  have key : ∀ g, (σ h).appTop ((σ g).appTop r) = (σ (h * g)).appTop r := by
    intro g
    rw [← hσ, Scheme.Hom.comp_appTop]
    rfl
  simp only [key]
  exact Fintype.prod_equiv (Equiv.mulLeft h) _ _ (fun _ => rfl)

omit [Group G] in
theorem mem_basicOpen_norm (r : Γ(X, ⊤)) (x : X) :
    x ∈ X.basicOpen (norm σ r) ↔ ∀ g, σ g x ∈ X.basicOpen r := by
  rw [norm, mem_basicOpen_prod]
  simp only [Opens.mem_top, true_and, Finset.mem_univ, forall_const]
  refine forall_congr' fun g => ?_
  rw [← Scheme.preimage_basicOpen_top]
  rfl

end Norm

section Core

/-- An affine open around a finite set, saturated for an equivalence relation on points whose
classes are single orbits of a finite group away from a closed subscheme, and are fibres of a
closed map to a scheme with finite affine neighborhoods on that closed subscheme. -/
theorem exists_saturated_isAffineOpen {W Z P : Scheme.{u}} [W.IsQuasiAffine]
    {G : Type*} [Group G] [Fintype G] (σ : G → (W ⟶ W)) (hσ1 : σ 1 = 𝟙 W)
    (hσ : ∀ g h, σ g ≫ σ h = σ (g * h))
    (rel : W → W → Prop) (hrel : Equivalence rel) (hfin : ∀ w, {w' | rel w w'}.Finite)
    (hσrel : ∀ g w, rel w (σ g w))
    (i : Z ⟶ W) [IsClosedImmersion i] (q : Z ⟶ P) (hq : IsClosedMap q)
    (hP : PointTopology.HasFiniteAffineNeighborhoods P)
    (hsat : ∀ z w, rel (i z) w → w ∈ Set.range i)
    (hqrel : ∀ z z', rel (i z) (i z') ↔ q z = q z')
    (horbit : ∀ w w', w ∉ Set.range i → rel w w' → ∃ g, σ g w = w')
    (F : Set W) (hF : F.Finite) :
    ∃ V : W.Opens, IsAffineOpen V ∧ F ⊆ V ∧ ∀ w w', rel w w' → w ∈ V → w' ∈ V := by
  classical
  have hσ1x : ∀ w, σ 1 w = w := fun w => by rw [hσ1]; rfl
  have hσσ : ∀ g k w, σ k (σ g w) = σ (g * k) w := fun g k w => by
    rw [← Scheme.Hom.comp_apply, hσ]
  have hi_inj : Function.Injective i := i.isClosedEmbedding.injective
  -- the saturation `Fs` of `F` and its orbit `FG`
  set Fs : Set W := ⋃ w ∈ F, {w' | rel w w'} with hFs_def
  have hmemFs : ∀ w', w' ∈ Fs ↔ ∃ w ∈ F, rel w w' := fun w' => by
    simp [hFs_def]
  have hFs_fin : Fs.Finite := hF.biUnion fun w _ => hfin w
  have hF_Fs : F ⊆ Fs := fun w hw => (hmemFs w).mpr ⟨w, hw, hrel.refl w⟩
  have hFs_sat : ∀ w w', w ∈ Fs → rel w w' → w' ∈ Fs := fun w w' hw hww' => by
    obtain ⟨v, hv, hvw⟩ := (hmemFs w).mp hw
    exact (hmemFs w').mpr ⟨v, hv, hrel.trans hvw hww'⟩
  set FG : Set W := ⋃ g, σ g '' Fs
  have hFG_fin : FG.Finite := Set.finite_iUnion fun g => hFs_fin.image _
  -- a `G`-stable affine basic open `X` containing `Fs`
  obtain ⟨s, hsFG, hs_aff⟩ := exists_basicOpen_isAffineOpen_of_finite W hFG_fin
  set X : W.Opens := W.basicOpen (norm σ s) with hX_def
  have hX_mem : ∀ x, x ∈ X ↔ ∀ g, σ g x ∈ W.basicOpen s := mem_basicOpen_norm σ s
  have hXs : X ≤ W.basicOpen s := fun x hx => by
    simpa [hσ1x] using (hX_mem x).mp hx 1
  have hX_aff : IsAffineOpen X := by
    have := hs_aff.basicOpen (W.presheaf.map (homOfLE le_top).op (norm σ s))
    rwa [Scheme.basicOpen_res, inf_eq_right.mpr hXs] at this
  have hX_pre : ∀ g, σ g ⁻¹ᵁ X = X := fun g => by
    rw [hX_def, Scheme.preimage_basicOpen_top, appTop_norm σ hσ]
  have hX_stable : ∀ g, X ≤ σ g ⁻¹ᵁ X := fun g => (hX_pre g).ge
  have hFs_X : Fs ⊆ X := fun x hx => (hX_mem x).mpr fun g =>
    hsFG (Set.mem_iUnion.mpr ⟨g, x, hx, rfl⟩)
  -- the closed part
  have hZ0_aff : IsAffineOpen (i ⁻¹ᵁ X) := hX_aff.preimage i
  set E : Set Z := i ⁻¹' Fs
  have hE_fin : E.Finite := hFs_fin.preimage hi_inj.injOn
  obtain ⟨⟨V1, hV1⟩, hqE⟩ := hP (q '' E) (hE_fin.image q)
  obtain ⟨z, hzE, hzle⟩ := exists_basicOpen_of_isAffineOpen hZ0_aff hE_fin
    (V := i ⁻¹ᵁ X ⊓ q ⁻¹ᵁ V1) (fun x hx => ⟨hFs_X hx, hqE ⟨x, hx, rfl⟩⟩) inf_le_left
  set B : Set P := q '' ((Z.basicOpen z : Set Z)ᶜ)
  have hB : IsClosed B := hq _ (Z.basicOpen z).isOpen.isClosed_compl
  have hEB : ∀ x ∈ E, q x ∉ B := by
    rintro x hx ⟨y, hy, hxy⟩
    exact hy (hzE (hFs_sat _ _ hx ((hqrel x y).mpr hxy.symm)))
  obtain ⟨c, hcE, hcle⟩ := exists_basicOpen_of_isAffineOpen hV1 (hE_fin.image q)
    (V := V1 ⊓ ⟨Bᶜ, hB.isOpen_compl⟩)
    (by rintro _ ⟨x, hx, rfl⟩; exact ⟨hqE ⟨x, hx, rfl⟩, hEB x hx⟩) inf_le_left
  have hcz : q ⁻¹ᵁ P.basicOpen c ≤ Z.basicOpen z := fun y hy => by
    by_contra hyz
    exact (hcle hy).2 ⟨y, hyz, rfl⟩
  -- a section `φ` over `i ⁻¹ X` with `D(φ) = q ⁻¹ D(c)`
  set c' : Γ(Z, Z.basicOpen z) := q.appLE V1 (Z.basicOpen z) (hzle.trans inf_le_right) c
  have hc' : Z.basicOpen c' = q ⁻¹ᵁ P.basicOpen c := by
    rw [Scheme.basicOpen_appLE, inf_eq_right.mpr hcz]
  obtain ⟨n, y, hy⟩ := exists_eq_pow_mul_of_isAffineOpen Z _ hZ0_aff z c'
  have hφ : Z.basicOpen (z * y) = q ⁻¹ᵁ P.basicOpen c := by
    have hunit : IsUnit ((z |_ Z.basicOpen z) ^ n) :=
      IsUnit.pow _ (RingedSpace.isUnit_res_basicOpen _ z)
    have h1 : Z.basicOpen (y |_ Z.basicOpen z) = Z.basicOpen c' := by
      rw [hy, Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit Z hunit,
        inf_eq_right.mpr (Scheme.basicOpen_le _ _)]
    rw [Scheme.basicOpen_mul, ← hc', ← h1]
    exact (Scheme.basicOpen_res Z _ _).symm
  -- lift `φ` and correct it by the ideal of the closed part
  obtain ⟨h0, hh0⟩ := i.app_surjective X hX_aff (z * y)
  set I : Ideal Γ(W, X) := RingHom.ker (i.app X).hom
  have hI : ∀ (w : W) (hw : w ∈ X), w ∉ Set.range i → ¬ I ≤ pointIdeal w hw := by
    intro w hw hwi hle
    obtain ⟨a, hwa, hale⟩ := exists_basicOpen_of_isAffineOpen hX_aff (Set.finite_singleton w)
      (V := X ⊓ ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩)
      (Set.singleton_subset_iff.mpr ⟨hw, hwi⟩) inf_le_left
    have hbot : Z.basicOpen (i.app X a) = ⊥ := by
      rw [← Scheme.preimage_basicOpen]
      ext x
      simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hx => (hale hx).2 ⟨x, rfl⟩
    obtain ⟨m, hm⟩ := (Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact
      hZ0_aff.isCompact _).mpr hbot
    have hamI : a ^ m ∈ I := by
      simp [I, RingHom.mem_ker, map_pow, hm]
    have hap : a ∈ pointIdeal w hw := (inferInstance : (pointIdeal w hw).IsPrime).mem_of_pow_mem
      m (hle hamI)
    exact (mem_pointIdeal w hw a).mp hap (hwa rfl)
  set T : Set X := {x | x.1 ∈ Fs ∧ x.1 ∉ Set.range i}
  have hT_fin : T.Finite :=
    (hFs_fin.preimage Subtype.val_injective.injOn).subset fun x hx => hx.1
  obtain ⟨e, heI, he⟩ := exists_add_notMem_of_finite I h0 hT_fin (fun x => pointIdeal x.1 x.2)
    (fun _ _ => inferInstance) (fun x hx => hI x.1 x.2 hx.2)
  set h : Γ(W, X) := h0 + e
  have hh_pre : i ⁻¹ᵁ W.basicOpen h = q ⁻¹ᵁ P.basicOpen c := by
    have he0 : i.app X e = 0 := heI
    rw [Scheme.preimage_basicOpen, map_add, he0, add_zero, hh0, hφ]
  have hh_le : W.basicOpen h ≤ X := Scheme.basicOpen_le _ _
  have hFs_h : Fs ⊆ W.basicOpen h := by
    intro w hw
    by_cases hwi : w ∈ Set.range i
    · obtain ⟨x, rfl⟩ := hwi
      have : x ∈ i ⁻¹ᵁ W.basicOpen h := by
        rw [hh_pre]; exact hcE ⟨x, hw, rfl⟩
      exact this
    · have := he ⟨w, hFs_X hw⟩ ⟨hw, hwi⟩
      rw [mem_pointIdeal, not_not] at this
      exact this
  -- the norm of `h` along `G`
  set hG : Γ(W, X) := ∏ g, (σ g).appLE X X (hX_stable g) h
  have hV_mem : ∀ w, w ∈ W.basicOpen hG ↔ w ∈ X ∧ ∀ g, σ g w ∈ W.basicOpen h := by
    intro w
    rw [mem_basicOpen_prod]
    simp only [Finset.mem_univ, forall_const, Scheme.basicOpen_appLE, Opens.mem_inf]
    constructor
    · rintro ⟨hw, H⟩
      exact ⟨hw, fun g => (H g).2⟩
    · rintro ⟨hw, H⟩
      exact ⟨hw, fun g => ⟨hw, H g⟩⟩
  refine ⟨W.basicOpen hG, hX_aff.basicOpen hG, fun w hw => ?_, ?_⟩
  · exact (hV_mem w).mpr ⟨hFs_X (hF_Fs hw), fun g =>
      hFs_h (hFs_sat _ _ (hF_Fs hw) (hσrel g w))⟩
  intro w w' hww' hw
  obtain ⟨hwX, hwh⟩ := (hV_mem w).mp hw
  rw [hV_mem]
  by_cases hwi : w ∈ Set.range i
  · obtain ⟨x, rfl⟩ := hwi
    have hqx : x ∈ q ⁻¹ᵁ P.basicOpen c := by
      have h1 := hwh 1
      rw [hσ1x] at h1
      rw [← hh_pre]
      exact h1
    have key : ∀ x', rel (i x) (i x') → i x' ∈ W.basicOpen h := by
      intro x' hxx'
      have : x' ∈ q ⁻¹ᵁ P.basicOpen c := by
        show q x' ∈ P.basicOpen c
        rw [← (hqrel x x').mp hxx']
        exact hqx
      rw [← hh_pre] at this
      exact this
    obtain ⟨x', rfl⟩ := hsat x w' hww'
    refine ⟨hh_le (key x' hww'), fun k => ?_⟩
    obtain ⟨x'', hx''⟩ := hsat x' _ (hσrel k (i x'))
    rw [← hx'']
    exact key x'' (hrel.trans hww' (hx'' ▸ hσrel k (i x')))
  · obtain ⟨g, rfl⟩ := horbit w w' hwi hww'
    refine ⟨hX_stable g hwX, fun k => ?_⟩
    rw [hσσ]
    exact hwh _

end Core

end Langlands.AlgebraicGeometry.OrbitSaturatedAffineOpen
