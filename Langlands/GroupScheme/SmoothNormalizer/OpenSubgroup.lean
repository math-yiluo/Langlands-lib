import Langlands.GroupScheme.SmoothNormalizer.KrullSection
import Langlands.GroupScheme.CorepresentedClosedSubgroup
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Spectrum.Prime.Chevalley

/-! # Closed subgroups of smooth groups with connected fibres containing all jets

Let `C` corepresent a group-valued functor on commutative `A`-algebras, with `C` smooth over `A`
and with connected fibres over every point of `Spec A`. A closed subgroup cut out by a finitely
generated ideal `K` which contains every infinitesimal neighbourhood of the identity section is
everything: `K = ⊥`.
-/

universe u

open CategoryTheory TensorProduct

namespace Langlands.GroupScheme.SmoothNormalizer

section Flat

/-- Along a flat ring map `f`, an element `r` killed after base change by an element outside a
prime `Q` is killed by an element of the source whose image is outside `Q`. -/
theorem exists_mul_eq_zero_of_flat {R T : Type*} [CommRing R] [CommRing T] (f : R →+* T)
    (hf : f.Flat) {r : R} {τ : T} {Q : Ideal T} (hτ : τ ∉ Q) (h : τ * f r = 0) :
    ∃ s : R, s * r = 0 ∧ f s ∉ Q := by
  let _ := f.toAlgebra
  have : Module.Flat R T := hf
  have h' : ∑ _i : Unit, r • τ = 0 := by
    rw [Fintype.sum_unique, Algebra.smul_def, mul_comm]
    exact h
  obtain ⟨k, a, y, hy, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero
    (f := fun _ : Unit => r) (x := fun _ : Unit => τ) h'
  by_contra hcon
  push Not at hcon
  apply hτ
  have hτy : τ = ∑ j, a () j • y j := hy ()
  rw [hτy]
  refine Ideal.sum_mem _ fun j _ => ?_
  rw [Algebra.smul_def]
  refine Q.mul_mem_right _ (hcon _ ?_)
  have := ha j
  rw [Fintype.sum_unique] at this
  rw [mul_comm]
  exact this

/-- If every element of a finitely generated ideal `K` is killed by an element of a submonoid `M`,
then a single element of `M` kills all of `K`. -/
theorem exists_mem_forall_mul_eq_zero_of_fg {R : Type*} [CommRing R] {K : Ideal R} (hK : K.FG)
    (M : Submonoid R) (h : ∀ k ∈ K, ∃ s ∈ M, s * k = 0) : ∃ s ∈ M, ∀ k ∈ K, s * k = 0 := by
  classical
  obtain ⟨S, rfl⟩ := hK
  choose s hs using fun (g : S) => h g (Ideal.subset_span g.2)
  refine ⟨∏ g, s g, Submonoid.prod_mem _ fun g _ => (hs g).1, fun k hk => ?_⟩
  induction hk using Submodule.span_induction with
  | mem g hg =>
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ ⟨g, hg⟩), mul_assoc, (hs ⟨g, hg⟩).2,
      mul_zero]
  | zero => rw [mul_zero]
  | add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]
  | smul a x _ hx => rw [smul_eq_mul, mul_left_comm, hx, mul_zero]

/-- If every element of a finitely generated ideal `K` is killed by an element whose image under
`f` avoids the prime `Q`, then a single such element kills all of `K`. -/
theorem exists_forall_mul_eq_zero_of_fg {R T : Type*} [CommRing R] [CommRing T] (f : R →+* T)
    {K : Ideal R} (hK : K.FG) {Q : Ideal T} [Q.IsPrime]
    (h : ∀ k ∈ K, ∃ s : R, s * k = 0 ∧ f s ∉ Q) :
    ∃ s : R, (∀ k ∈ K, s * k = 0) ∧ f s ∉ Q := by
  classical
  obtain ⟨S, rfl⟩ := hK
  choose s hs using fun (g : S) => h g (Ideal.subset_span g.2)
  refine ⟨∏ g, s g, fun k hk => ?_, ?_⟩
  · induction hk using Submodule.span_induction with
    | mem g hg =>
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ ⟨g, hg⟩), mul_assoc, (hs ⟨g, hg⟩).1,
        mul_zero]
    | zero => rw [mul_zero]
    | add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]
    | smul a x _ hx => rw [smul_eq_mul, mul_left_comm, hx, mul_zero]
  · rw [map_prod]
    exact fun hmem => (Ideal.IsPrime.prod_mem_iff.1 hmem).elim fun g ⟨_, hg⟩ => (hs g).2 hg

end Flat

section Points

open Langlands.GroupScheme.Corepresented

variable {A : CommRingCat.{u}} {F : CommAlgCat.{u} A ⥤ GrpCat.{u}} {C : CommAlgCat.{u} A}
  (e : (F ⋙ forget GrpCat).CorepresentableBy C)

/-- The classifying algebra map of a point. -/
abbrev cls {B : CommAlgCat.{u} A} (x : F.obj B) : C →ₐ[A] B := (e.homEquiv.symm x).hom

variable {e}

theorem cls_map {B B' : CommAlgCat.{u} A} (f : B ⟶ B') (x : F.obj B) :
    cls e (F.map f x) = f.hom.comp (cls e x) := by
  have h : e.homEquiv.symm (F.map f x) = e.homEquiv.symm x ≫ f :=
    (e.homEquiv_symm_comp x f).symm
  rw [cls, h]
  rfl

theorem eq_of_cls_eq {B : CommAlgCat.{u} A} {x y : F.obj B} (h : cls e x = cls e y) : x = y := by
  apply e.homEquiv.symm.injective
  exact CommAlgCat.hom_ext h

variable (e) in
/-- `x` is good at `Q` for the ideal `K`: some annihilator of `K` is mapped outside `Q` by the
classifying map of `x`. Geometrically, the image of the point lies in the open locus where `K`
vanishes. -/
def Good (K : Ideal C) {B : CommAlgCat.{u} A} (x : F.obj B) (Q : Ideal B) : Prop :=
  ∃ t : C, (∀ k ∈ K, t * k = 0) ∧ cls e x t ∉ Q

variable {K : Ideal C}

theorem good_map_iff {B B' : CommAlgCat.{u} A} (f : B ⟶ B') (x : F.obj B) (Q : Ideal B') :
    Good e K (F.map f x) Q ↔ Good e K x (Q.comap f.hom) := by
  unfold Good
  rw [cls_map]
  rfl

theorem map_eq_iff {B B' : CommAlgCat.{u} A} (f : B ⟶ B') (x : F.obj B) (y : F.obj B') :
    F.map f x = y ↔ f.hom.comp (cls e x) = cls e y := by
  rw [← cls_map]
  exact ⟨fun h => h ▸ rfl, eq_of_cls_eq⟩

omit e in
theorem map_ofHom_id {X : Type u} [CommRing X] [Algebra A X] (x : F.obj (CommAlgCat.of A X)) :
    F.map (CommAlgCat.ofHom (AlgHom.id A X)) x = x := by
  rw [show CommAlgCat.ofHom (AlgHom.id A X) = 𝟙 (CommAlgCat.of A X) from rfl, F.map_id]
  rfl

variable (e) in
/-- The universal point over `C`. -/
abbrev univ : F.obj C := e.homEquiv (𝟙 C)

theorem cls_univ : cls e (univ e) = AlgHom.id A C := by
  rw [cls, Equiv.symm_apply_apply]
  rfl

theorem map_cls_univ {B : CommAlgCat.{u} A} (x : F.obj B) :
    F.map (e.homEquiv.symm x) (univ e) = x := by
  rw [map_eq_iff, cls_univ]
  rfl

variable (e) in
/-- The antipode of `C`: the classifying map of the inverse of the universal point. -/
abbrev antipode : C →ₐ[A] C := cls e (univ e)⁻¹

theorem cls_inv {B : CommAlgCat.{u} A} (x : F.obj B) :
    cls e x⁻¹ = (cls e x).comp (antipode e) := by
  have h : x⁻¹ = F.map (e.homEquiv.symm x) (univ e)⁻¹ := by rw [map_inv, map_cls_univ]
  rw [h, cls_map]

theorem antipode_antipode (c : C) : antipode e (antipode e c) = c := by
  have h := cls_inv (e := e) (univ e)⁻¹
  rw [inv_inv, cls_univ] at h
  exact (DFunLike.congr_fun h c).symm

variable {Z : ∀ B : CommAlgCat.{u} A, Subgroup (F.obj B)}

theorem mem_of_cls_kills (hK : Corepresented.IsCutOutBy e Z K) {B : CommAlgCat.{u} A}
    {x : F.obj B} (h : ∀ k ∈ K, cls e x k = 0) : x ∈ Z B :=
  (hK B x).2 h

theorem antipode_mem (hK : Corepresented.IsCutOutBy e Z K) {k : C} (hk : k ∈ K) :
    antipode e k ∈ K := by
  let π : C ⟶ CommAlgCat.of A (C ⧸ K) := CommAlgCat.ofHom (Ideal.Quotient.mkₐ A K)
  have h1 : F.map π (univ e) ∈ Z _ := mem_of_cls_kills hK fun b hb => by
    rw [cls_map, cls_univ]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hb
  have h2 := (hK _ _).1 (inv_mem h1) k hk
  change cls e (F.map π (univ e))⁻¹ k = 0 at h2
  rw [← map_inv, cls_map] at h2
  exact Ideal.Quotient.eq_zero_iff_mem.1 h2

theorem good_inv (hK : Corepresented.IsCutOutBy e Z K) {B : CommAlgCat.{u} A} {x : F.obj B}
    {Q : Ideal B} (hx : Good e K x Q) : Good e K x⁻¹ Q := by
  obtain ⟨t, ht, htQ⟩ := hx
  refine ⟨antipode e t, fun k hk => ?_, ?_⟩
  · have : antipode e t * k = antipode e (t * antipode e k) := by
      rw [map_mul, antipode_antipode]
    rw [this, ht _ (antipode_mem hK hk), map_zero]
  · rw [cls_inv, AlgHom.comp_apply, antipode_antipode]
    exact htQ

section Square

variable (e)

/-- The coordinate algebra `C ⊗[A] C` of the square. -/
abbrev sq : CommAlgCat.{u} A := CommAlgCat.of A (C ⊗[A] C)

/-- The first universal point over the square. -/
abbrev pt₁ : F.obj (sq (C := C)) := e.homEquiv (CommAlgCat.ofHom Algebra.TensorProduct.includeLeft)

/-- The second universal point over the square. -/
abbrev pt₂ : F.obj (sq (C := C)) := e.homEquiv (CommAlgCat.ofHom Algebra.TensorProduct.includeRight)

/-- The comultiplication: the classifying map of the product of the two universal points. -/
abbrev comul : C →ₐ[A] C ⊗[A] C := cls e (pt₁ e * pt₂ e)

variable {e}

theorem cls_pt₁ : cls e (pt₁ e) = Algebra.TensorProduct.includeLeft := by
  rw [cls, Equiv.symm_apply_apply]
  rfl

theorem cls_pt₂ : cls e (pt₂ e) = Algebra.TensorProduct.includeRight := by
  rw [cls, Equiv.symm_apply_apply]
  rfl

/-- The algebra map out of the square classifying a pair of points. -/
abbrev pair {B : CommAlgCat.{u} A} (f g : C →ₐ[A] B) : sq (C := C) ⟶ B :=
  CommAlgCat.ofHom (Algebra.TensorProduct.lift f g fun _ _ => .all _ _)

theorem map_pair_pt₁ {B : CommAlgCat.{u} A} (x z : F.obj B) :
    F.map (pair (cls e x) (cls e z)) (pt₁ e) = x := by
  rw [map_eq_iff, cls_pt₁]
  ext c
  simp [pair]

theorem map_pair_pt₂ {B : CommAlgCat.{u} A} (x z : F.obj B) :
    F.map (pair (cls e x) (cls e z)) (pt₂ e) = z := by
  rw [map_eq_iff, cls_pt₂]
  ext c
  simp [pair]

variable (e) in
/-- The shear map `(x, z) ↦ (x z, z)` on coordinates. -/
abbrev shear : C ⊗[A] C →ₐ[A] C ⊗[A] C :=
  Algebra.TensorProduct.lift (comul e) Algebra.TensorProduct.includeRight fun _ _ => .all _ _

variable (e) in
/-- The inverse shear `(x, z) ↦ (x z⁻¹, z)` on coordinates. -/
abbrev shearInv : C ⊗[A] C →ₐ[A] C ⊗[A] C :=
  Algebra.TensorProduct.lift (cls e (pt₁ e * (pt₂ e)⁻¹)) Algebra.TensorProduct.includeRight
    fun _ _ => .all _ _

theorem map_shear_pt₁ : F.map (CommAlgCat.ofHom (shear e)) (pt₁ e) = pt₁ e * pt₂ e := by
  rw [map_eq_iff, cls_pt₁]
  ext c
  simp

theorem map_shear_pt₂ : F.map (CommAlgCat.ofHom (shear e)) (pt₂ e) = pt₂ e := by
  rw [map_eq_iff, cls_pt₂]
  ext c
  simp

theorem map_shearInv_pt₁ :
    F.map (CommAlgCat.ofHom (shearInv e)) (pt₁ e) = pt₁ e * (pt₂ e)⁻¹ := by
  rw [map_eq_iff, cls_pt₁]
  ext c
  simp

theorem map_shearInv_pt₂ : F.map (CommAlgCat.ofHom (shearInv e)) (pt₂ e) = pt₂ e := by
  rw [map_eq_iff, cls_pt₂]
  ext c
  simp

/-- Two algebra maps out of the square agreeing on both universal points are equal. -/
theorem sq_hom_ext {B : CommAlgCat.{u} A} {f g : C ⊗[A] C →ₐ[A] B}
    (h₁ : F.map (CommAlgCat.ofHom f) (pt₁ e) = F.map (CommAlgCat.ofHom g) (pt₁ e))
    (h₂ : F.map (CommAlgCat.ofHom f) (pt₂ e) = F.map (CommAlgCat.ofHom g) (pt₂ e)) : f = g := by
  rw [map_eq_iff, cls_map, cls_pt₁] at h₁
  rw [map_eq_iff, cls_map, cls_pt₂] at h₂
  exact Algebra.TensorProduct.ext h₁ h₂

theorem shear_comp_shearInv : (shear e).comp (shearInv e) = AlgHom.id A _ := by
  apply sq_hom_ext (e := e) (B := sq (C := C))
  · rw [CommAlgCat.ofHom_comp, F.map_comp, ConcreteCategory.comp_apply, map_shearInv_pt₁, map_mul,
      map_inv, map_shear_pt₁, map_shear_pt₂, mul_inv_cancel_right]
    exact (map_ofHom_id _).symm
  · rw [CommAlgCat.ofHom_comp, F.map_comp, ConcreteCategory.comp_apply, map_shearInv_pt₂,
      map_shear_pt₂]
    exact (map_ofHom_id _).symm

theorem shearInv_comp_shear : (shearInv e).comp (shear e) = AlgHom.id A _ := by
  apply sq_hom_ext (e := e) (B := sq (C := C))
  · rw [CommAlgCat.ofHom_comp, F.map_comp, ConcreteCategory.comp_apply, map_shear_pt₁, map_mul,
      map_shearInv_pt₁, map_shearInv_pt₂, inv_mul_cancel_right]
    exact (map_ofHom_id _).symm
  · rw [CommAlgCat.ofHom_comp, F.map_comp, ConcreteCategory.comp_apply, map_shear_pt₂,
      map_shearInv_pt₂]
    exact (map_ofHom_id _).symm

/-- The comultiplication is flat: it is the left inclusion followed by the shear isomorphism. -/
theorem comul_flat [Module.Flat A C] : (comul e).toRingHom.Flat := by
  have h : (comul e).toRingHom = (shear e).toRingHom.comp (algebraMap C (C ⊗[A] C)) := by
    ext c
    simp [← Algebra.TensorProduct.one_def]
  rw [h]
  refine RingHom.Flat.comp (RingHom.flat_algebraMap_iff.2 inferInstance)
    (RingHom.Flat.of_bijective ⟨?_, ?_⟩)
  · intro x y hxy
    have := congrArg (shearInv e) hxy
    change (shearInv e).comp (shear e) x = (shearInv e).comp (shear e) y at this
    rwa [shearInv_comp_shear] at this
  · intro y
    refine ⟨shearInv e y, ?_⟩
    change (shear e).comp (shearInv e) y = y
    rw [shear_comp_shearInv]
    rfl

/-- The universal case of `good_mul`. -/
theorem good_mul_univ (hK : Corepresented.IsCutOutBy e Z K) (hfg : K.FG) [Module.Flat A C]
    {Q : Ideal (C ⊗[A] C)} [Q.IsPrime] (hx : Good e K (pt₁ e) Q) (hz : Good e K (pt₂ e) Q) :
    Good e K (pt₁ e * pt₂ e) Q := by
  obtain ⟨t₁, ht₁, hq₁⟩ := hx
  obtain ⟨t₂, ht₂, hq₂⟩ := hz
  rw [cls_pt₁] at hq₁
  rw [cls_pt₂] at hq₂
  set τ : C ⊗[A] C := (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] C) t₁ *
    (Algebra.TensorProduct.includeRight : C →ₐ[A] C ⊗[A] C) t₂
  have hτ : τ ∉ Q := fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hq₁ hq₂
  -- The ideal of `Z × Z` inside the square.
  set 𝔟 : Ideal (C ⊗[A] C) :=
    Ideal.map (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] C) K ⊔
      Ideal.map (Algebra.TensorProduct.includeRight : C →ₐ[A] C ⊗[A] C) K
  have hΔ : ∀ k ∈ K, comul e k ∈ 𝔟 := by
    intro k hk
    let π : sq (C := C) ⟶ CommAlgCat.of A ((C ⊗[A] C) ⧸ 𝔟) :=
      CommAlgCat.ofHom (Ideal.Quotient.mkₐ A 𝔟)
    have h1 : F.map π (pt₁ e) ∈ Z _ := mem_of_cls_kills hK fun b hb => by
      rw [cls_map, cls_pt₁]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hb))
    have h2 : F.map π (pt₂ e) ∈ Z _ := mem_of_cls_kills hK fun b hb => by
      rw [cls_map, cls_pt₂]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hb))
    have h3 := (hK _ _).1 (mul_mem h1 h2) k hk
    change cls e (F.map π (pt₁ e) * F.map π (pt₂ e)) k = 0 at h3
    rw [← map_mul, cls_map] at h3
    exact Ideal.Quotient.eq_zero_iff_mem.1 h3
  have hann : 𝔟 ≤ (Ideal.span {τ}).annihilator := by
    apply sup_le
    · rw [Ideal.map_le_iff_le_comap]
      intro k hk
      rw [Ideal.mem_comap, Submodule.mem_annihilator_span_singleton, smul_eq_mul]
      change Algebra.TensorProduct.includeLeft k *
        (Algebra.TensorProduct.includeLeft t₁ * Algebra.TensorProduct.includeRight t₂) = 0
      rw [← mul_assoc, ← map_mul, mul_comm k t₁, ht₁ k hk, map_zero, zero_mul]
    · rw [Ideal.map_le_iff_le_comap]
      intro k hk
      rw [Ideal.mem_comap, Submodule.mem_annihilator_span_singleton, smul_eq_mul]
      change Algebra.TensorProduct.includeRight k *
        (Algebra.TensorProduct.includeLeft t₁ * Algebra.TensorProduct.includeRight t₂) = 0
      rw [mul_left_comm, ← map_mul, mul_comm k t₂, ht₂ k hk, map_zero, mul_zero]
  have hkill : ∀ k ∈ K, τ * comul e k = 0 := fun k hk => by
    have := hann (hΔ k hk)
    rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul] at this
    rw [mul_comm]
    exact this
  obtain ⟨s, hs, hsQ⟩ := exists_forall_mul_eq_zero_of_fg (comul e).toRingHom hfg (Q := Q)
    fun k hk => exists_mul_eq_zero_of_flat _ comul_flat hτ (hkill k hk)
  exact ⟨s, hs, hsQ⟩

/-- Goodness is stable under products, at prime ideals. -/
theorem good_mul (hK : Corepresented.IsCutOutBy e Z K) (hfg : K.FG) [Module.Flat A C]
    {B : CommAlgCat.{u} A} {x z : F.obj B} {Q : Ideal B} [Q.IsPrime] (hx : Good e K x Q)
    (hz : Good e K z Q) : Good e K (x * z) Q := by
  set ψ := pair (cls e x) (cls e z)
  have h1 : F.map ψ (pt₁ e) = x := map_pair_pt₁ x z
  have h2 : F.map ψ (pt₂ e) = z := map_pair_pt₂ x z
  have hxz : x * z = F.map ψ (pt₁ e * pt₂ e) := by rw [map_mul, h1, h2]
  rw [hxz, good_map_iff]
  rw [← h1, good_map_iff] at hx
  rw [← h2, good_map_iff] at hz
  have : (Q.comap ψ.hom).IsPrime := Ideal.comap_isPrime _ _
  exact good_mul_univ hK hfg hx hz

end Square

end Points

section Fibre

open Langlands.GroupScheme.Corepresented

variable {A : CommRingCat.{u}} {F : CommAlgCat.{u} A ⥤ GrpCat.{u}} {C : CommAlgCat.{u} A}
  {e : (F ⋙ forget GrpCat).CorepresentableBy C} {K : Ideal C}
  {Z : ∀ B : CommAlgCat.{u} A, Subgroup (F.obj B)}

variable (e) in
/-- The counit: the classifying map of the identity point over `A`. -/
abbrev counit : C →ₐ[A] A := cls e (1 : F.obj (CommAlgCat.of A A))

theorem cls_one (B : CommAlgCat.{u} A) :
    cls e (1 : F.obj B) = (Algebra.ofId A B).comp (counit e) := by
  have h : (1 : F.obj B) =
      F.map (CommAlgCat.ofHom (Algebra.ofId A B)) (1 : F.obj (CommAlgCat.of A A)) :=
    (map_one _).symm
  rw [h, cls_map]
  rfl

theorem good_one {s : C} (hs : ∀ k ∈ K, s * k = 0) (hs1 : counit e s = 1)
    {B : CommAlgCat.{u} A} {Q : Ideal B} (hQ : Q ≠ ⊤) : Good e K (1 : F.obj B) Q :=
  ⟨s, hs, by
    rw [cls_one, AlgHom.comp_apply, hs1, map_one]
    exact fun h => hQ ((Ideal.eq_top_iff_one _).2 h)⟩

theorem isOpen_good {B : CommAlgCat.{u} A} (x : F.obj B) :
    IsOpen {Q : PrimeSpectrum B | Good e K x Q.asIdeal} := by
  have h : {Q : PrimeSpectrum B | Good e K x Q.asIdeal} =
      ⋃ (t : C) (_ : ∀ k ∈ K, t * k = 0), (PrimeSpectrum.basicOpen (cls e x t) : Set _) := by
    ext Q
    simp [Good]
  rw [h]
  exact isOpen_iUnion fun t => isOpen_iUnion fun _ => (PrimeSpectrum.basicOpen _).isOpen

variable (e) in
/-- The universal point of the fibre `k ⊗[A] C` over an `A`-field `k`. -/
abbrev fibrePt (k : Type u) [Field k] [Algebra A k] : F.obj (CommAlgCat.of A (k ⊗[A] C)) :=
  F.map (CommAlgCat.ofHom (Algebra.TensorProduct.includeRight : C →ₐ[A] k ⊗[A] C)) (univ e)

/-- **Cosets of the good locus.** A point `y` of the fibre `k ⊗[A] C` outside the good locus has an
open neighbourhood outside it: the image, under the open projection from `(k ⊗[A] C) ⊗[k] κ`, of
the good locus translated by the point `y` itself, defined over its residue field `κ`. -/
theorem exists_isOpen_not_good (hK : IsCutOutBy e Z K) (hfg : K.FG) [Module.Flat A C] {s : C}
    (hs : ∀ k ∈ K, s * k = 0) (hs1 : counit e s = 1)
    {k : Type u} [Field k] [Algebra A k]
    {κ : Type u} [Field κ] [Algebra (k ⊗[A] C) κ] [Algebra k κ] [IsScalarTower k (k ⊗[A] C) κ]
    [Algebra A κ] [IsScalarTower A (k ⊗[A] C) κ] [IsScalarTower A k κ]
    (y : PrimeSpectrum (k ⊗[A] C)) (hker : RingHom.ker (algebraMap (k ⊗[A] C) κ) = y.asIdeal)
    (hy : ¬ Good e K (fibrePt e k) y.asIdeal) :
    ∃ O : Set (PrimeSpectrum (k ⊗[A] C)),
      O ⊆ {P | ¬ Good e K (fibrePt e k) P.asIdeal} ∧ IsOpen O ∧ y ∈ O := by
  let ιE : CommAlgCat.of A (k ⊗[A] C) ⟶ CommAlgCat.of A ((k ⊗[A] C) ⊗[k] κ) :=
    CommAlgCat.ofHom (IsScalarTower.toAlgHom A (k ⊗[A] C) ((k ⊗[A] C) ⊗[k] κ))
  let res : CommAlgCat.of A (k ⊗[A] C) ⟶ CommAlgCat.of A κ :=
    CommAlgCat.ofHom (IsScalarTower.toAlgHom A (k ⊗[A] C) κ)
  let ικ : CommAlgCat.of A κ ⟶ CommAlgCat.of A ((k ⊗[A] C) ⊗[k] κ) :=
    CommAlgCat.ofHom ((Algebra.TensorProduct.includeRight :
      κ →ₐ[k] (k ⊗[A] C) ⊗[k] κ).restrictScalars A)
  let ev : CommAlgCat.of A ((k ⊗[A] C) ⊗[k] κ) ⟶ CommAlgCat.of A κ :=
    CommAlgCat.ofHom ((Algebra.TensorProduct.lift (IsScalarTower.toAlgHom k (k ⊗[A] C) κ)
      (AlgHom.id k κ) fun _ _ => .all _ _).restrictScalars A)
  have hf1 : ικ ≫ ev = 𝟙 _ := by
    refine CommAlgCat.hom_ext (AlgHom.ext fun a => ?_)
    change (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom k (k ⊗[A] C) κ) (AlgHom.id k κ)
      (fun _ _ => .all _ _)) ((1 : k ⊗[A] C) ⊗ₜ[k] a) = a
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl
  have hf2 : ιE ≫ ev = res := by
    refine CommAlgCat.hom_ext (AlgHom.ext fun c => ?_)
    change (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom k (k ⊗[A] C) κ) (AlgHom.id k κ)
      (fun _ _ => .all _ _)) (algebraMap (k ⊗[A] C) ((k ⊗[A] C) ⊗[k] κ) c) =
      algebraMap (k ⊗[A] C) κ c
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.TensorProduct.lift_tmul, map_one, mul_one]
    rfl
  let uE := F.map ιE (fibrePt e k)
  let ybar := F.map res (fibrePt e k)
  let yE := F.map ικ ybar
  have hp1 : F.map ev yE = ybar := by
    change F.map ev (F.map ικ ybar) = ybar
    rw [← ConcreteCategory.comp_apply, ← F.map_comp, hf1, F.map_id]
    rfl
  have hp2 : F.map ev uE = ybar := by
    change F.map ev (F.map ιE (fibrePt e k)) = _
    rw [← ConcreteCategory.comp_apply, ← F.map_comp, hf2]
  have hres : (⊥ : Ideal κ).comap res.hom = y.asIdeal := by
    rw [← hker, RingHom.ker_eq_comap_bot]
    rfl
  refine ⟨PrimeSpectrum.comap (algebraMap (k ⊗[A] C) ((k ⊗[A] C) ⊗[k] κ)) ''
    {Q | Good e K (yE⁻¹ * uE) Q.asIdeal}, ?_, ?_, ?_⟩
  · rintro _ ⟨Q, hQ, rfl⟩ hgood
    apply hy
    have h1 : Good e K uE Q.asIdeal := (good_map_iff ιE _ Q.asIdeal).2 hgood
    have h2 := good_mul hK hfg h1 (good_inv hK hQ)
    have h3 : uE * (yE⁻¹ * uE)⁻¹ = yE := by group
    rw [h3] at h2
    change Good e K (F.map ικ ybar) Q.asIdeal at h2
    rw [good_map_iff] at h2
    have hbot : Q.asIdeal.comap ικ.hom = ⊥ :=
      ((Ideal.eq_bot_or_top _).resolve_right (Ideal.comap_isPrime ικ.hom Q.asIdeal).ne_top)
    rw [hbot] at h2
    change Good e K (F.map res (fibrePt e k)) ⊥ at h2
    rw [good_map_iff, hres] at h2
    exact h2
  · exact PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field _
      (isOpen_good (B := CommAlgCat.of A ((k ⊗[A] C) ⊗[k] κ)) (yE⁻¹ * uE))
  · refine ⟨⟨RingHom.ker ev.hom, RingHom.ker_isPrime _⟩, ?_, ?_⟩
    · change Good e K (yE⁻¹ * uE) (RingHom.ker ev.hom)
      rw [RingHom.ker_eq_comap_bot, ← good_map_iff, map_mul, map_inv, hp1, hp2, inv_mul_cancel]
      exact good_one hs hs1 bot_ne_top
    · ext x
      change ev.hom (algebraMap (k ⊗[A] C) ((k ⊗[A] C) ⊗[k] κ) x) = 0 ↔ x ∈ y.asIdeal
      rw [← hker, RingHom.mem_ker]
      have := congrArg (fun f => f.hom x) hf2
      exact Iff.of_eq (congrArg (· = (0 : κ)) this)

/-- **The fibre argument.** Over a field `k` with connected fibre `Spec (k ⊗[A] C)`, the good
locus is open and closed and contains the identity, hence is everything. -/
theorem good_fibrePt (hK : IsCutOutBy e Z K) (hfg : K.FG) [Module.Flat A C] {s : C}
    (hs : ∀ k ∈ K, s * k = 0) (hs1 : counit e s = 1)
    {k : Type u} [Field k] [Algebra A k] [ConnectedSpace (PrimeSpectrum (k ⊗[A] C))]
    (q : PrimeSpectrum (k ⊗[A] C)) : Good e K (fibrePt e k) q.asIdeal := by
  set V := {P : PrimeSpectrum (k ⊗[A] C) | Good e K (fibrePt e k) P.asIdeal}
  have hVo : IsOpen V := isOpen_good (B := CommAlgCat.of A (k ⊗[A] C)) (fibrePt e k)
  have hVc : IsClosed V := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro y hy
    have : IsScalarTower k (k ⊗[A] C) y.asIdeal.ResidueField :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    have : IsScalarTower A k y.asIdeal.ResidueField :=
      IsScalarTower.of_algebraMap_eq fun a => by
        rw [IsScalarTower.algebraMap_apply A (k ⊗[A] C) y.asIdeal.ResidueField,
          IsScalarTower.algebraMap_apply A k (k ⊗[A] C),
          ← IsScalarTower.algebraMap_apply k (k ⊗[A] C) y.asIdeal.ResidueField]
    exact exists_isOpen_not_good hK hfg hs hs1 (κ := y.asIdeal.ResidueField) y
      (Ideal.ker_algebraMap_residueField _) hy
  -- The identity point of the fibre is good.
  let ev₀ : CommAlgCat.of A (k ⊗[A] C) ⟶ CommAlgCat.of A k :=
    CommAlgCat.ofHom ((Algebra.TensorProduct.lift (AlgHom.id k k)
      ((Algebra.ofId A k).comp (counit e)) fun _ _ => .all _ _).restrictScalars A)
  have hev₀ : F.map ev₀ (fibrePt e k) = 1 := by
    rw [map_eq_iff, cls_map, cls_univ, cls_one]
    ext c
    change (Algebra.TensorProduct.lift (AlgHom.id k k) ((Algebra.ofId A k).comp (counit e))
      (fun _ _ => .all _ _)) ((1 : k) ⊗ₜ[A] c) = _
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  have hVne : V.Nonempty := by
    refine ⟨⟨RingHom.ker ev₀.hom, RingHom.ker_isPrime _⟩, ?_⟩
    change Good e K (fibrePt e k) (RingHom.ker ev₀.hom)
    rw [RingHom.ker_eq_comap_bot, ← good_map_iff, hev₀]
    exact good_one hs hs1 bot_ne_top
  have hV : V = Set.univ := (isClopen_iff.1 ⟨hVc, hVo⟩).resolve_left hVne.ne_empty
  have hq : q ∈ V := hV ▸ Set.mem_univ q
  exact hq

/-- **A closed subgroup with connected fibres containing every infinitesimal neighbourhood of
the identity is everything.** Let `C` be smooth over `A` with connected fibres over every point of
`Spec A`. If a family of subgroups is cut out by a finitely generated ideal `K` contained in every
power of the augmentation ideal, then `K = ⊥`. -/
theorem eq_bot_of_forall_le_pow [Algebra.Smooth A C]
    (hconn : ∀ p : PrimeSpectrum A,
      ConnectedSpace (PrimeSpectrum (p.asIdeal.ResidueField ⊗[A] C)))
    (hK : IsCutOutBy e Z K) (hfg : K.FG) (hle : ∀ n : ℕ, K ≤ RingHom.ker (counit e) ^ n) :
    K = ⊥ := by
  let M : Submonoid C :=
    { carrier := {s | counit e s = 1}
      mul_mem' := fun {a b} ha hb => by
        change counit e (a * b) = 1
        rw [map_mul, show counit e a = 1 from ha, show counit e b = 1 from hb, one_mul]
      one_mem' := map_one _ }
  obtain ⟨s, hs1, hs⟩ := exists_mem_forall_mul_eq_zero_of_fg hfg M fun k hk => by
    obtain ⟨s, h1, h2⟩ := exists_mul_eq_zero_of_forall_mem_pow (counit e) fun n => hle n hk
    exact ⟨s, h1, h2⟩
  have hgood : ∀ P : PrimeSpectrum C, Good e K (univ e) P.asIdeal := by
    intro P
    let p := PrimeSpectrum.comap (algebraMap A C) P
    have := hconn p
    let q := PrimeSpectrum.preimageEquivFiber A C p ⟨P, rfl⟩
    have hq : q.asIdeal.comap
        (Algebra.TensorProduct.includeRight : C →ₐ[A] p.asIdeal.ResidueField ⊗[A] C) =
          P.asIdeal := by
      have h := (PrimeSpectrum.preimageEquivFiber A C p).symm_apply_apply ⟨P, rfl⟩
      exact congrArg (fun x => x.1.asIdeal) h
    have h := good_fibrePt hK hfg hs hs1 q
    rw [fibrePt, good_map_iff] at h
    rw [← hq]
    exact h
  by_contra hne
  have hann : Submodule.annihilator K ≠ ⊤ := by
    intro htop
    apply hne
    rw [eq_bot_iff]
    intro k hk
    have h1 : (1 : C) ∈ Submodule.annihilator K := htop ▸ Submodule.mem_top
    have := (Submodule.mem_annihilator.1 h1) k hk
    rw [one_smul] at this
    exact this
  obtain ⟨Mx, hMx, hle'⟩ := Ideal.exists_le_maximal _ hann
  obtain ⟨t, ht, htM⟩ := hgood ⟨Mx, hMx.isPrime⟩
  rw [cls_univ] at htM
  exact htM (hle' (Submodule.mem_annihilator.2 fun k hk => by rw [smul_eq_mul]; exact ht k hk))

end Fibre

end Langlands.GroupScheme.SmoothNormalizer
