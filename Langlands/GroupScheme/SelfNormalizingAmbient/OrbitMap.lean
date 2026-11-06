import Langlands.GroupScheme.SelfNormalizingAmbient.Stabilizer
import Langlands.GroupScheme.CorepresentedPoints
import Langlands.RingTheory.Grassmannian.ProperFinitePresentation
import Langlands.RingTheory.Grassmannian.BaseChangeMembership
import Mathlib.Algebra.Exact.Basic

/-! # The orbit map of a cut-out subscheme into a Grassmannian

See the paired Markdown.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct CategoryTheory.MonObj CategoryTheory.Obj

namespace Module

variable {S : Type u} [CommRing S] {V : Type u} [AddCommGroup V] [Module S V] {k : ℕ}

namespace Grassmannian

/-- Two points of a Grassmannian, one contained in the other, are equal. -/
theorem eq_of_le {N₁ N₂ : G(k, V; S)} (h : (N₁ : Submodule S V) ≤ N₂) : N₁ = N₂ := by
  set f := Submodule.factor h
  obtain ⟨l, hl⟩ :=
    Module.projective_lifting_property f LinearMap.id (Submodule.factor_surjective h)
  obtain ⟨eq, -, -⟩ := (LinearMap.exact_subtype_ker_map f).splitSurjectiveEquiv
    (Submodule.injective_subtype _) ⟨l, hl⟩
  have : Module.Finite S (LinearMap.ker f) :=
    Module.Finite.of_surjective (LinearMap.fst S _ _ ∘ₗ eq.toLinearMap)
      (fun x => ⟨eq.symm (x, 0), by simp⟩)
  have : Module.Projective S (LinearMap.ker f) :=
    Module.Projective.of_split (eq.symm.toLinearMap ∘ₗ LinearMap.inl S _ _)
      (LinearMap.fst S _ _ ∘ₗ eq.toLinearMap) (by ext x; simp)
  have hrank : rankAtStalk (R := S) (LinearMap.ker f) = 0 := by
    funext p
    have h₁ := congrFun (rankAtStalk_eq_of_equiv eq) p
    rw [rankAtStalk_prod, Pi.add_apply, N₁.rankAtStalk_eq, N₂.rankAtStalk_eq] at h₁
    simp only [Pi.zero_apply]
    omega
  have := (rankAtStalk_eq_zero_iff_subsingleton).1 hrank
  apply Module.Grassmannian.ext
  ext x
  refine ⟨fun hx => h hx, fun hx => ?_⟩
  have hk : Submodule.mkQ N₁.toSubmodule x ∈ LinearMap.ker f := by
    rw [LinearMap.mem_ker, Submodule.factor_mk, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact hx
  have h0 := congrArg Subtype.val (Subsingleton.elim (⟨_, hk⟩ : LinearMap.ker f) 0)
  simp only [Submodule.mkQ_apply, ZeroMemClass.coe_zero, Submodule.Quotient.mk_eq_zero] at h0
  exact h0

/-- The kernel of a surjection onto a module isomorphic to `S ^ k`, as a point of
`G(k, V; S)`. -/
def ofKer {N : Type u} [AddCommGroup N] [Module S N] (Φ : V →ₗ[S] N)
    (hΦ : Function.Surjective Φ) (eN : N ≃ₗ[S] (Fin k → S)) : G(k, V; S) where
  toSubmodule := LinearMap.ker Φ
  finite_quotient := Module.Finite.equiv ((Φ.quotKerEquivOfSurjective hΦ).trans eN).symm
  projective_quotient :=
    Module.Projective.of_equiv ((Φ.quotKerEquivOfSurjective hΦ).trans eN).symm
  rankAtStalk_eq p := by
    have : Nontrivial S := PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨p⟩
    rw [rankAtStalk_eq_of_equiv ((Φ.quotKerEquivOfSurjective hΦ).trans eN)]
    simp

end Grassmannian

/-- A finite projective module is a direct summand of a finite free module, with a finite
projective complement. -/
theorem exists_prod_linearEquiv_pi (R : Type u) [CommRing R] (P : Type u) [AddCommGroup P]
    [Module R P] [Module.Finite R P] [Module.Projective R P] :
    ∃ (b : ℕ) (C : Submodule R (Fin b → R)), Module.Finite R C ∧ Module.Projective R C ∧
      Nonempty ((P × C) ≃ₗ[R] (Fin b → R)) := by
  obtain ⟨b, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R P
  obtain ⟨eq, -, -⟩ := (LinearMap.exact_subtype_ker_map f).splitSurjectiveEquiv
    (Submodule.injective_subtype _) ⟨g, hfg⟩
  exact ⟨b, LinearMap.ker f,
    Module.Finite.of_surjective (LinearMap.fst R _ _ ∘ₗ eq.toLinearMap)
      (fun x => ⟨eq.symm (x, 0), by simp⟩),
    Module.Projective.of_split (eq.symm.toLinearMap ∘ₗ LinearMap.inl R _ _)
      (LinearMap.fst R _ _ ∘ₗ eq.toLinearMap) (by ext x; simp),
    ⟨(LinearEquiv.prodComm R P _).trans eq.symm⟩⟩

end Module

namespace Langlands.GroupScheme.Corepresented

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}} {B : CommAlgCat.{u} R}
  {e : (F ⋙ forget GrpCat).CorepresentableBy B}

section Conjugation

variable (e) in
/-- The conjugate `g u g⁻¹` of the universal cut point `u` over `S ⊗[R] (B ⧸ L)` by the image
of `g ∈ F S`. -/
def universalCutConj (L : Ideal B) {S : CommAlgCat.{u} R} (g : F.obj S) :
    F.obj (tensorQuotient L S) :=
  F.map (tensorQuotientLeft L S) g * universalCutPoint e L S *
    (F.map (tensorQuotientLeft L S) g)⁻¹

theorem map_map_eq_map_comp {A A' A'' : CommAlgCat.{u} R} (f : A ⟶ A') (f' : A' ⟶ A'')
    (x : F.obj A) : F.map f' (F.map f x) = F.map (f ≫ f') x := by
  rw [F.map_comp, ConcreteCategory.comp_apply]

theorem map_universalCutConj {L : Ideal B} {S A' : CommAlgCat.{u} R} (g : F.obj S)
    (χ : tensorQuotient L S ⟶ A') :
    F.map χ (universalCutConj e L g) = F.map (tensorQuotientLeft L S ≫ χ) g *
      F.map χ (universalCutPoint e L S) * (F.map (tensorQuotientLeft L S ≫ χ) g)⁻¹ := by
  rw [universalCutConj, map_mul, map_mul, map_inv, map_map_eq_map_comp]

theorem universalCutConj_one (L : Ideal B) (S : CommAlgCat.{u} R) :
    universalCutConj e L (1 : F.obj S) = universalCutPoint e L S := by
  rw [universalCutConj, map_one, one_mul, inv_one, mul_one]

/-- Algebra maps out of `S ⊗[R] (B ⧸ L)` are determined by their restriction to `S` and by the
image of the universal cut point. -/
theorem tensorQuotient_hom_ext {L : Ideal B} {S A' : CommAlgCat.{u} R}
    {χ₁ χ₂ : tensorQuotient L S ⟶ A'}
    (hl : tensorQuotientLeft L S ≫ χ₁ = tensorQuotientLeft L S ≫ χ₂)
    (hu : F.map χ₁ (universalCutPoint e L S) = F.map χ₂ (universalCutPoint e L S)) :
    χ₁ = χ₂ := by
  have h := congrArg e.homEquiv.symm hu
  rw [homEquiv_symm_map, homEquiv_symm_map, universalCutPoint, Equiv.symm_apply_apply] at h
  have hr : ∀ c : B ⧸ L, χ₁.hom (1 ⊗ₜ c) = χ₂.hom (1 ⊗ₜ c) := by
    intro c
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
    exact congrArg (fun φ : B ⟶ A' => φ.hom b) h
  have hs : ∀ s : S, χ₁.hom (s ⊗ₜ 1) = χ₂.hom (s ⊗ₜ 1) :=
    fun s => congrArg (fun φ : S ⟶ A' => φ.hom s) hl
  ext1
  refine Algebra.TensorProduct.ext' fun s c => ?_
  have hsc : (s ⊗ₜ c : S ⊗[R] (B ⧸ L)) = (s ⊗ₜ 1) * (1 ⊗ₜ c) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [hsc, map_mul, map_mul, hs, hr]

variable (e) in
/-- The algebra map `S ⊗[R] (B ⧸ L₁) ⟶ S ⊗[R] (B ⧸ L₂)` over `S` classifying the conjugate
`universalCutConj e L₂ g`, when that conjugate vanishes on `L₁`. -/
def conjMap (L₁ L₂ : Ideal B) {S : CommAlgCat.{u} R} (g : F.obj S)
    (h : VanishesOn e L₁ (universalCutConj e L₂ g)) : tensorQuotient L₁ S ⟶ tensorQuotient L₂ S :=
  CommAlgCat.ofHom (Algebra.TensorProduct.lift (tensorQuotientLeft L₂ S).hom
    (Ideal.Quotient.liftₐ L₁ (e.homEquiv.symm (universalCutConj e L₂ g)).hom h)
    fun _ _ => Commute.all _ _)

variable {L₁ L₂ : Ideal B} {S : CommAlgCat.{u} R} (g : F.obj S)
  (h : VanishesOn e L₁ (universalCutConj e L₂ g))

theorem left_conjMap : tensorQuotientLeft L₁ S ≫ conjMap e L₁ L₂ g h = tensorQuotientLeft L₂ S := by
  ext s
  simp [conjMap]

theorem map_conjMap :
    F.map (conjMap e L₁ L₂ g h) (universalCutPoint e L₁ S) = universalCutConj e L₂ g := by
  rw [universalCutPoint]
  erw [← e.homEquiv_comp]
  rw [← Equiv.apply_symm_apply e.homEquiv (universalCutConj e L₂ g)]
  congr 1
  ext b
  simp only [conjMap, CommAlgCat.hom_comp, CommAlgCat.hom_ofHom, AlgHom.coe_comp,
    Function.comp_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  exact Ideal.Quotient.lift_mk _ _ _

end Conjugation

section Orbit

/-- The base change `S ⊗[R] (B ⧸ L) ⟶ S' ⊗[R] (B ⧸ L)` of `φ : S ⟶ S'`. -/
abbrev tensorQuotientBaseChange (L : Ideal B) {S S' : CommAlgCat.{u} R} (φ : S ⟶ S') :
    tensorQuotient L S ⟶ tensorQuotient L S' :=
  CommAlgCat.ofHom (Algebra.TensorProduct.map φ.hom (AlgHom.id R (B ⧸ L)))

theorem left_tensorQuotientBaseChange (L : Ideal B) {S S' : CommAlgCat.{u} R} (φ : S ⟶ S') :
    tensorQuotientLeft L S ≫ tensorQuotientBaseChange L φ = φ ≫ tensorQuotientLeft L S' := by
  ext s
  simp

theorem map_tensorQuotientBaseChange (L : Ideal B) {S S' : CommAlgCat.{u} R} (φ : S ⟶ S') :
    F.map (tensorQuotientBaseChange L φ) (universalCutPoint e L S) = universalCutPoint e L S' := by
  rw [universalCutPoint, universalCutPoint]
  erw [← e.homEquiv_comp]
  congr 1
  ext b
  change Algebra.TensorProduct.map φ.hom (AlgHom.id R (B ⧸ L)) (1 ⊗ₜ Ideal.Quotient.mk L b) =
    1 ⊗ₜ Ideal.Quotient.mk L b
  simp

variable (e) in
/-- The automorphism of `S ⊗[R] (B ⧸ I ^ m)` over `S` classifying the conjugate of the universal
point of the `(m - 1)`-st infinitesimal neighbourhood of the unit by `g ∈ F S`. -/
def jetMap (m : ℕ) {S : CommAlgCat.{u} R} (g : F.obj S) :
    tensorQuotient (augIdeal e ^ m) S ⟶ tensorQuotient (augIdeal e ^ m) S :=
  conjMap e _ _ g ((vanishesOn_universalCutPoint S).conj _)

variable (e) in
/-- The surjection `S ⊗[R] (B ⧸ I ^ m) ⟶ S ⊗[R] (B ⧸ K)` over `S` classifying the conjugate
`g u g⁻¹` of the universal point `u` of the subscheme cut out by `K ⊇ I ^ m`. -/
def orbitMap {m : ℕ} {K : Ideal B} (hK : augIdeal e ^ m ≤ K) {S : CommAlgCat.{u} R}
    (g : F.obj S) : tensorQuotient (augIdeal e ^ m) S ⟶ tensorQuotient K S :=
  conjMap e _ _ g (((vanishesOn_universalCutPoint S).mono hK).conj _)

variable {m : ℕ} {K : Ideal B} (hK : augIdeal e ^ m ≤ K) {S : CommAlgCat.{u} R}

theorem left_jetMap (g : F.obj S) :
    tensorQuotientLeft _ S ≫ jetMap e m g = tensorQuotientLeft _ S :=
  left_conjMap _ _

theorem map_jetMap (g : F.obj S) :
    F.map (jetMap e m g) (universalCutPoint e _ S) = universalCutConj e (augIdeal e ^ m) g :=
  map_conjMap _ _

theorem left_orbitMap (g : F.obj S) :
    tensorQuotientLeft _ S ≫ orbitMap e hK g = tensorQuotientLeft K S :=
  left_conjMap _ _

theorem map_orbitMap (g : F.obj S) :
    F.map (orbitMap e hK g) (universalCutPoint e _ S) = universalCutConj e K g :=
  map_conjMap _ _

theorem jetMap_inv_comp (g : F.obj S) : jetMap e m g⁻¹ ≫ jetMap e m g = 𝟙 _ := by
  refine tensorQuotient_hom_ext (e := e) ?_ ?_
  · rw [← Category.assoc, left_jetMap, left_jetMap, Category.comp_id]
  · rw [F.map_comp, ConcreteCategory.comp_apply, map_jetMap, map_universalCutConj, left_jetMap,
      map_jetMap, F.map_id, ConcreteCategory.id_apply, universalCutConj, map_inv]
    group

theorem orbitMap_eq_jetMap_comp (g : F.obj S) :
    orbitMap e hK g = jetMap e m g ≫ orbitMap e hK 1 := by
  refine tensorQuotient_hom_ext (e := e) ?_ ?_
  · rw [← Category.assoc, left_jetMap, left_orbitMap, left_orbitMap]
  · rw [F.map_comp, ConcreteCategory.comp_apply, map_jetMap, map_universalCutConj, left_orbitMap,
      map_orbitMap, map_orbitMap, universalCutConj_one, universalCutConj]

theorem orbitMap_one_tmul (s : S) (b : B) :
    (orbitMap e hK 1).hom (s ⊗ₜ Ideal.Quotient.mk _ b) = s ⊗ₜ Ideal.Quotient.mk K b := by
  have hb : (e.homEquiv.symm (universalCutConj e K (1 : F.obj S))).hom b =
      (1 : S) ⊗ₜ Ideal.Quotient.mk K b := by
    rw [universalCutConj_one, universalCutPoint, Equiv.symm_apply_apply]
    rfl
  change (s ⊗ₜ 1 : S ⊗[R] (B ⧸ K)) * (e.homEquiv.symm (universalCutConj e K 1)).hom b = _
  rw [hb, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem orbitMap_one_surjective : Function.Surjective (orbitMap e hK (1 : F.obj S)).hom := by
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul s q =>
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact ⟨_, orbitMap_one_tmul hK s b⟩
  | add x y hx hy =>
    obtain ⟨x', rfl⟩ := hx
    obtain ⟨y', rfl⟩ := hy
    exact ⟨x' + y', map_add _ _ _⟩

theorem jetMap_surjective (g : F.obj S) : Function.Surjective (jetMap e m g).hom := by
  intro x
  refine ⟨(jetMap e m g⁻¹).hom x, ?_⟩
  have h := congrArg (fun χ => χ.hom x) (jetMap_inv_comp g)
  simpa using h

theorem orbitMap_surjective (g : F.obj S) : Function.Surjective (orbitMap e hK g).hom := by
  rw [orbitMap_eq_jetMap_comp hK g, CommAlgCat.hom_comp, AlgHom.coe_comp]
  exact (orbitMap_one_surjective hK).comp (jetMap_surjective g)

/-- **Kernel criterion.** An algebra map `χ` out of `S ⊗[R] (B ⧸ I ^ m)` kills the kernel of the
orbit map of `g` exactly when conjugating the image of the universal point by the image of `g`
gives a point vanishing on `K`. -/
theorem le_ker_orbitMap_iff (g : F.obj S) {A' : CommAlgCat.{u} R}
    (χ : tensorQuotient (augIdeal e ^ m) S ⟶ A') :
    RingHom.ker (orbitMap e hK g).hom ≤ RingHom.ker χ.hom ↔
      VanishesOn e K ((F.map (tensorQuotientLeft _ S ≫ χ) g)⁻¹ *
        F.map χ (universalCutPoint e _ S) * F.map (tensorQuotientLeft _ S ≫ χ) g) := by
  set q := orbitMap e hK g
  constructor
  · intro h
    let ψ : tensorQuotient K S ⟶ A' := CommAlgCat.ofHom
      ((Ideal.Quotient.liftₐ (RingHom.ker q.hom) χ.hom fun a ha => h ha).comp
        (Ideal.quotientKerAlgEquivOfSurjective (orbitMap_surjective hK g)).symm.toAlgHom)
    have hψ : q ≫ ψ = χ := by
      refine CommAlgCat.hom_ext (AlgHom.ext fun x => ?_)
      change Ideal.Quotient.liftₐ (RingHom.ker q.hom) χ.hom (fun a ha => h ha)
        ((Ideal.quotientKerAlgEquivOfSurjective (orbitMap_surjective hK g)).symm
          ((Ideal.quotientKerAlgEquivOfSurjective (orbitMap_surjective hK g))
            (Ideal.Quotient.mk _ x))) = χ.hom x
      rw [AlgEquiv.symm_apply_apply]
      rfl
    have hu : F.map χ (universalCutPoint e _ S) =
        F.map (tensorQuotientLeft _ S ≫ χ) g * F.map ψ (universalCutPoint e K S) *
          (F.map (tensorQuotientLeft _ S ≫ χ) g)⁻¹ := by
      rw [← hψ, F.map_comp, ConcreteCategory.comp_apply, map_orbitMap, map_universalCutConj,
        ← Category.assoc, left_orbitMap]
    rw [hu]
    have hv := (vanishesOn_universalCutPoint (e := e) (K := K) S).map ψ
    convert hv using 1
    group
  · intro hx
    obtain ⟨ψ, hψl, hψu⟩ := exists_universalCutPoint_of_vanishesOn _ hx
    have hψ : q ≫ ψ = χ := by
      refine tensorQuotient_hom_ext (e := e) ?_ ?_
      · rw [← Category.assoc, left_orbitMap, hψl]
      · rw [F.map_comp, ConcreteCategory.comp_apply, map_orbitMap, map_universalCutConj, hψl, hψu]
        group
    intro a ha
    rw [RingHom.mem_ker] at ha ⊢
    rw [← hψ, CommAlgCat.hom_comp, AlgHom.comp_apply, ha, map_zero]

/-- **Two orbit maps have the same kernel exactly when `g⁻¹ h` stabilizes the subscheme cut out
by `K`.** -/
theorem ker_orbitMap_eq_iff (g h : F.obj S) :
    RingHom.ker (orbitMap e hK g).hom = RingHom.ker (orbitMap e hK h).hom ↔
      Stabilizes e K (g⁻¹ * h) := by
  rw [le_antisymm_iff, le_ker_orbitMap_iff, le_ker_orbitMap_iff, stabilizes_iff_universal,
    left_orbitMap, left_orbitMap, map_orbitMap, map_orbitMap, universalCutConj, universalCutConj,
    map_mul, map_inv]
  refine and_congr ?_ ?_
  · convert Iff.rfl using 2
    group
  · convert Iff.rfl using 2
    group

theorem tensorQuotientBaseChange_apply (L : Ideal B) {S' : CommAlgCat.{u} R} (φ : S ⟶ S')
    (z : S ⊗[R] (B ⧸ L)) :
    (tensorQuotientBaseChange L φ).hom z = φ.hom.toLinearMap.rTensor (B ⧸ L) z := by
  induction z with
  | tmul s q => rfl
  | add z z' hz hz' => rw [map_add, map_add, hz, hz']

/-- The orbit maps are compatible with base change. -/
theorem orbitMap_comp_baseChange {S' : CommAlgCat.{u} R} (φ : S ⟶ S') (g : F.obj S) :
    orbitMap e hK g ≫ tensorQuotientBaseChange K φ =
      tensorQuotientBaseChange _ φ ≫ orbitMap e hK (F.map φ g) := by
  refine tensorQuotient_hom_ext (e := e) ?_ ?_
  · rw [← Category.assoc, left_orbitMap, left_tensorQuotientBaseChange, ← Category.assoc,
      left_tensorQuotientBaseChange, Category.assoc, left_orbitMap]
  · rw [F.map_comp (orbitMap e hK g), ConcreteCategory.comp_apply, map_orbitMap,
      map_universalCutConj,
      left_tensorQuotientBaseChange, map_tensorQuotientBaseChange,
      F.map_comp (tensorQuotientBaseChange _ φ), ConcreteCategory.comp_apply,
      map_tensorQuotientBaseChange, map_orbitMap, universalCutConj, map_map_eq_map_comp]

end Orbit

section Linear

variable {m : ℕ} {K : Ideal B} (hK : augIdeal e ^ m ≤ K) {S : CommAlgCat.{u} R}

theorem smul_eq_tmul_one_mul {A : Type u} [CommRing A] [Algebra R A] (s : S) (y : S ⊗[R] A) :
    s • y = (s ⊗ₜ[R] (1 : A)) * y := by
  induction y with
  | tmul s' a => rw [TensorProduct.smul_tmul', Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      smul_eq_mul]
  | add y y' hy hy' => rw [smul_add, mul_add, hy, hy']

variable (e) in
/-- The orbit map of `g` as an `S`-linear map. -/
def orbitLinearMap (g : F.obj S) : S ⊗[R] (B ⧸ augIdeal e ^ m) →ₗ[S] S ⊗[R] (B ⧸ K) where
  toFun := (orbitMap e hK g).hom
  map_add' := map_add _
  map_smul' s x := by
    have h : (orbitMap e hK g).hom (s ⊗ₜ 1) = s ⊗ₜ 1 :=
      congrArg (fun χ => χ.hom s) (left_orbitMap hK g)
    rw [RingHom.id_apply, smul_eq_tmul_one_mul, smul_eq_tmul_one_mul, map_mul, h]

theorem orbitLinearMap_apply (g : F.obj S) (x : S ⊗[R] (B ⧸ augIdeal e ^ m)) :
    orbitLinearMap e hK g x = (orbitMap e hK g).hom x :=
  rfl

theorem ker_orbitLinearMap_eq_iff (g h : F.obj S) :
    LinearMap.ker (orbitLinearMap e hK g) = LinearMap.ker (orbitLinearMap e hK h) ↔
      Stabilizes e K (g⁻¹ * h) := by
  rw [← ker_orbitMap_eq_iff hK g h]
  simp only [SetLike.ext_iff, LinearMap.mem_ker, RingHom.mem_ker, orbitLinearMap_apply]

theorem orbitLinearMap_rTensor {S' : CommAlgCat.{u} R} (φ : S ⟶ S') (g : F.obj S)
    (z : S ⊗[R] (B ⧸ augIdeal e ^ m)) :
    orbitLinearMap e hK (F.map φ g) (φ.hom.toLinearMap.rTensor _ z) =
      φ.hom.toLinearMap.rTensor _ (orbitLinearMap e hK g z) := by
  have h := congrArg (fun χ => χ.hom z) (orbitMap_comp_baseChange hK φ g)
  simp only [CommAlgCat.hom_comp, AlgHom.comp_apply] at h
  exact h.symm

variable (C : Type u) [AddCommGroup C] [Module R C]

variable (e) in
/-- The orbit map of `g` on the first factor of `S ⊗[R] ((B ⧸ I ^ m) × C)`. -/
def orbitProdMap (g : F.obj S) :
    S ⊗[R] ((B ⧸ augIdeal e ^ m) × C) →ₗ[S] (S ⊗[R] (B ⧸ K)) × (S ⊗[R] C) :=
  ((orbitLinearMap e hK g).prodMap LinearMap.id) ∘ₗ
    (TensorProduct.prodRight R S S (B ⧸ augIdeal e ^ m) C).toLinearMap

theorem orbitProdMap_surjective (g : F.obj S) :
    Function.Surjective (orbitProdMap e hK C g) := by
  rw [orbitProdMap, LinearMap.coe_comp, LinearMap.coe_prodMap]
  exact (Function.Surjective.prodMap (orbitMap_surjective hK g) Function.surjective_id).comp
    (TensorProduct.prodRight R S S _ C).surjective

theorem orbitProdMap_rTensor {S' : CommAlgCat.{u} R} (φ : S ⟶ S') (g : F.obj S)
    (z : S ⊗[R] ((B ⧸ augIdeal e ^ m) × C)) :
    orbitProdMap e hK C (F.map φ g) (φ.hom.toLinearMap.rTensor _ z) =
      (φ.hom.toLinearMap.rTensor _ (orbitProdMap e hK C g z).1,
        φ.hom.toLinearMap.rTensor _ (orbitProdMap e hK C g z).2) := by
  induction z with
  | tmul s c =>
    simp only [orbitProdMap, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearMap.rTensor_tmul, TensorProduct.prodRight_tmul, LinearMap.prodMap_apply,
      LinearMap.id_apply, AlgHom.toLinearMap_apply]
    rw [← AlgHom.toLinearMap_apply, ← LinearMap.rTensor_tmul, orbitLinearMap_rTensor]
  | add z z' hz hz' => rw [map_add, map_add, hz, hz', map_add, Prod.fst_add, Prod.snd_add,
      map_add, map_add, Prod.mk_add_mk]

variable {C} {b : ℕ} (eW : ((B ⧸ K) × C) ≃ₗ[R] (Fin b → R))

/-- The identification of the target of the orbit maps with `S ^ b`. -/
def orbitTargetEquiv : ((S ⊗[R] (B ⧸ K)) × (S ⊗[R] C)) ≃ₗ[S] (Fin b → S) :=
  (TensorProduct.prodRight R S S (B ⧸ K) C).symm ≪≫ₗ eW.baseChange R S _ _ ≪≫ₗ
    TensorProduct.piScalarRight R S S (Fin b)

variable (e S) in
/-- The point of the Grassmannian `G(b, S ⊗[R] ((B ⧸ I ^ m) × C); S)` attached to `g ∈ F S`: the
kernel of its orbit map. -/
def orbitPoint (g : F.obj S) : Module.Grassmannian S (S ⊗[R] ((B ⧸ augIdeal e ^ m) × C)) b :=
  Module.Grassmannian.ofKer (orbitProdMap e hK C g) (orbitProdMap_surjective hK C g)
    (orbitTargetEquiv eW)

theorem orbitPoint_toSubmodule (g : F.obj S) :
    (orbitPoint e hK S eW g).toSubmodule = LinearMap.ker (orbitProdMap e hK C g) :=
  rfl

/-- **Two points have the same orbit point exactly when `g⁻¹ h` stabilizes the subscheme cut out
by `K`.** -/
theorem orbitPoint_eq_iff (g h : F.obj S) :
    orbitPoint e hK S eW g = orbitPoint e hK S eW h ↔ Stabilizes e K (g⁻¹ * h) := by
  rw [← ker_orbitLinearMap_eq_iff hK g h]
  constructor
  · intro H
    have H' := congrArg Module.Grassmannian.toSubmodule H
    rw [orbitPoint_toSubmodule, orbitPoint_toSubmodule] at H'
    ext w
    have := SetLike.ext_iff.1 H' ((TensorProduct.prodRight R S S _ C).symm (w, 0))
    simpa [orbitProdMap] using this
  · intro H
    apply Module.Grassmannian.ext
    change LinearMap.ker (orbitProdMap e hK C g) = LinearMap.ker (orbitProdMap e hK C h)
    ext z
    have := SetLike.ext_iff.1 H (TensorProduct.prodRight R S S _ C z).1
    simp only [LinearMap.mem_ker] at this
    simp [orbitProdMap, this]

/-- **The orbit points are compatible with base change.** -/
theorem map_orbitPoint {S' : CommAlgCat.{u} R} (φ : S ⟶ S') (g : F.obj S) :
    Module.Grassmannian.map φ.hom (orbitPoint e hK S eW g) =
      orbitPoint e hK S' eW (F.map φ g) := by
  apply Module.Grassmannian.eq_of_le
  change (Module.Grassmannian.map φ.hom (orbitPoint e hK S eW g)).toSubmodule ≤
    LinearMap.ker (orbitProdMap e hK C (F.map φ g))
  rw [Langlands.Grassmannian.map_toSubmodule_eq_span, Submodule.span_le]
  rintro _ ⟨z, hz, rfl⟩
  have hz' : orbitProdMap e hK C g z = 0 := hz
  rw [SetLike.mem_coe, LinearMap.mem_ker, orbitProdMap_rTensor, hz']
  simp

end Linear

section Scheme

variable {m : ℕ} {K : Ideal B} (hK : augIdeal e ^ m ≤ K) {C : Type u} [AddCommGroup C]
  [Module R C] {b : ℕ} (eW : ((B ⧸ K) × C) ≃ₗ[R] (Fin b → R)) {Gr : Scheme.{u}}
  {p : Gr ⟶ Spec R}
  (pt : ∀ (A : Type u) [CommRing A] [Algebra R A],
    Module.Grassmannian A (A ⊗[R] ((B ⧸ augIdeal e ^ m) × C)) b ≃
      {g : Spec (CommRingCat.of A) ⟶ Gr // g ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R A))})

variable (e) in
/-- The morphism `Spec S ⟶ Gr` over `Spec R` classifying the orbit point of `x ∈ F S`. -/
def orbitHom (S : CommAlgCat.{u} R) (x : F.obj S) : (algSpec R).obj (op S) ⟶ Over.mk p :=
  Over.homMk (pt S (orbitPoint e hK S eW x)).1 (pt S (orbitPoint e hK S eW x)).2

theorem orbitHom_left (S : CommAlgCat.{u} R) (x : F.obj S) :
    (orbitHom e hK eW pt S x).left = (pt S (orbitPoint e hK S eW x)).1 :=
  rfl

theorem orbitHom_eq_iff (S : CommAlgCat.{u} R) (x y : F.obj S) :
    orbitHom e hK eW pt S x = orbitHom e hK eW pt S y ↔ Stabilizes e K (x⁻¹ * y) := by
  rw [← orbitPoint_eq_iff hK eW x y]
  constructor
  · intro H
    have H' : (pt S (orbitPoint e hK S eW x)).1 = (pt S (orbitPoint e hK S eW y)).1 :=
      congrArg CommaMorphism.left H
    exact (pt S).injective (Subtype.ext H')
  · intro H
    ext1
    exact congrArg (fun N => (pt S N).1) H

variable {pt}
  (hpt : ∀ (A A' : Type u) [CommRing A] [CommRing A'] [Algebra R A] [Algebra R A']
    (φ : A →ₐ[R] A') (N : Module.Grassmannian A (A ⊗[R] ((B ⧸ augIdeal e ^ m) × C)) b),
    (pt A' (Module.Grassmannian.map φ N)).1 =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (pt A N).1)
include hpt

/-- The orbit morphisms are compatible with base change. -/
theorem map_orbitHom {S S' : CommAlgCat.{u} R} (φ : S ⟶ S') (x : F.obj S) :
    (algSpec R).map φ.op ≫ orbitHom e hK eW pt S x = orbitHom e hK eW pt S' (F.map φ x) := by
  ext1
  rw [Over.comp_left, orbitHom_left, orbitHom_left, ← map_orbitPoint, hpt]
  rfl

omit hpt in
theorem unit_comp_map_homEquiv_symm (T : Over (Spec R)) (g : T ⟶ (algSpec R).obj (op B)) :
    (algΓAlgSpecAdjunction R).unit.app T ≫
      (algSpec R).map (((algΓAlgSpecAdjunction R).homEquiv T (op B)).symm g) = g := by
  have h := (algΓAlgSpecAdjunction R).homEquiv_unit T (op B)
    (((algΓAlgSpecAdjunction R).homEquiv T (op B)).symm g)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- Composing a point with the orbit morphism of the universal point gives the orbit morphism of
the corresponding algebra point, precomposed with the affinization unit. -/
theorem comp_orbitHom (T : Over (Spec R)) (g : T ⟶ (groupScheme F e).X) :
    g ≫ orbitHom e hK eW pt B (e.homEquiv (𝟙 B)) =
      (algΓAlgSpecAdjunction R).unit.app T ≫
        orbitHom e hK eW pt ((algΓ R).obj T).unop (pointsEquiv F e T g) := by
  set φ := (((algΓAlgSpecAdjunction R).homEquiv T (op B)).symm g).unop
  have hg : (algΓAlgSpecAdjunction R).unit.app T ≫ (algSpec R).map φ.op = g :=
    unit_comp_map_homEquiv_symm T g
  have hP : pointsEquiv F e T g = e.homEquiv φ := pointsEquiv_apply F e T g
  have hφ : F.map φ (e.homEquiv (𝟙 B)) = e.homEquiv φ := by
    have h := e.homEquiv_comp φ (𝟙 B)
    rw [Category.id_comp] at h
    exact h.symm
  rw [hP, ← hφ, ← map_orbitHom hK eW hpt φ, ← Category.assoc]
  exact congrArg (fun f : T ⟶ (algSpec R).obj (op B) =>
    f ≫ orbitHom e hK eW pt B (e.homEquiv (𝟙 B))) hg.symm

/-- Over a test scheme whose affinization unit is an isomorphism, two points have the same
image exactly when `g⁻¹ h` stabilizes the subscheme cut out by `K`. -/
theorem comp_orbitHom_eq_iff_of_isIso (T : Over (Spec R))
    [IsIso ((algΓAlgSpecAdjunction R).unit.app T)] (g h : T ⟶ (groupScheme F e).X) :
    g ≫ orbitHom e hK eW pt B (e.homEquiv (𝟙 B)) = h ≫ orbitHom e hK eW pt B (e.homEquiv (𝟙 B)) ↔
      Stabilizes e K (pointsEquiv F e T (g⁻¹ * h)) := by
  rw [comp_orbitHom hK eW hpt, comp_orbitHom hK eW hpt, cancel_epi, orbitHom_eq_iff, map_mul,
    map_inv]

/-- **The fibres of the orbit morphism are the cosets of the stabilizer.** -/
theorem comp_orbitHom_eq_iff [Module.Projective R (B ⧸ K)] (T : Over (Spec R))
    (g h : T ⟶ (groupScheme F e).X) :
    g ≫ orbitHom e hK eW pt B (e.homEquiv (𝟙 B)) = h ≫ orbitHom e hK eW pt B (e.homEquiv (𝟙 B)) ↔
      Stabilizes e K (pointsEquiv F e T (g⁻¹ * h)) := by
  constructor
  · intro H
    set ψ := e.homEquiv.symm (pointsEquiv F e T (g⁻¹ * h))
    have hψ : pointsEquiv F e T (g⁻¹ * h) = e.homEquiv ψ := (e.homEquiv.apply_symm_apply _).symm
    rw [hψ, stabilizes_iff]
    intro a ha
    rw [RingHom.mem_ker]
    let 𝒰 := T.left.affineCover
    refine Scheme.zero_of_zero_cover (U := ⊤) (ψ.hom a) 𝒰 fun i => ?_
    let Ti : Over (Spec R) := Over.mk (𝒰.f i ≫ T.hom)
    let ai : Ti ⟶ T := Over.homMk (𝒰.f i) rfl
    have : IsIso ((algΓAlgSpecAdjunction R).unit.app Ti) :=
      (algΓAlgSpecAdjunction R).isIso_unit_app_iff_mem_essImage.mpr
        ((essImage_algSpec (R := R) (G := Ti)).mpr (inferInstanceAs (IsAffine (𝒰.X i))))
    have Hi := (comp_orbitHom_eq_iff_of_isIso hK eW hpt Ti (ai ≫ g) (ai ≫ h)).1
      ((Category.assoc ai g _).trans ((congrArg (ai ≫ ·) H).trans (Category.assoc ai h _).symm))
    rw [← GrpObj.comp_inv, ← MonObj.comp_mul, pointsEquiv_naturality, hψ] at Hi
    have hc : F.map ((algΓ R).map ai).unop (e.homEquiv ψ) =
        e.homEquiv (ψ ≫ ((algΓ R).map ai).unop) :=
      (e.homEquiv_comp ((algΓ R).map ai).unop ψ).symm
    rw [hc, stabilizes_iff] at Hi
    have := Hi ha
    rw [RingHom.mem_ker] at this
    exact this
  · intro H
    rw [comp_orbitHom hK eW hpt, comp_orbitHom hK eW hpt]
    rw [map_mul, map_inv, ← orbitHom_eq_iff hK eW pt] at H
    rw [H]

end Scheme

end Langlands.GroupScheme.Corepresented

namespace Langlands.GroupScheme.SelfNormalizingAmbient

open Corepresented

/-- **The orbit map.** For an ideal `K` of `B` containing a power `I ^ (n + 1)` of the
augmentation ideal, with `B ⧸ I ^ (n + 1)` and `B ⧸ K` finite projective, there is a proper,
locally finitely presented scheme `Y` over `Spec R` and a morphism `r` from the group scheme
whose fibres are exactly the cosets of the stabilizer of the subscheme cut out by `K`. -/
theorem exists_proper_orbit_map {R : CommRingCat.{u}} (F : CommAlgCat.{u} R ⥤ GrpCat.{u})
    {B : CommAlgCat.{u} R} (e : (F ⋙ forget GrpCat).CorepresentableBy B) (K : Ideal B) (n : ℕ)
    (hK : Corepresented.augIdeal e ^ (n + 1) ≤ K)
    [Module.Finite R (B ⧸ Corepresented.augIdeal e ^ (n + 1))]
    [Module.Projective R (B ⧸ Corepresented.augIdeal e ^ (n + 1))]
    [Module.Finite R (B ⧸ K)] [Module.Projective R (B ⧸ K)] :
    ∃ (Y : Over (Spec R)) (r : (Corepresented.groupScheme F e).X ⟶ Y),
      IsProper Y.hom ∧ LocallyOfFinitePresentation Y.hom ∧
      ∀ (T : Over (Spec R)) (g h : T ⟶ (Corepresented.groupScheme F e).X),
        g ≫ r = h ≫ r ↔
          Corepresented.Stabilizes e K (Corepresented.pointsEquiv F e T (g⁻¹ * h)) := by
  obtain ⟨c, C, hCf, hCp, ⟨eW⟩⟩ := Module.exists_prod_linearEquiv_pi R (B ⧸ K)
  obtain ⟨Gr, p, pt, hpt, hprop, hlfp⟩ :=
    Module.Grassmannian.exists_scheme_represents_isProper_locallyOfFinitePresentation R
      ((B ⧸ augIdeal e ^ (n + 1)) × C) c
  exact ⟨Over.mk p, orbitHom e hK eW pt B (e.homEquiv (𝟙 B)), hprop, hlfp,
    fun T g h => comp_orbitHom_eq_iff hK eW hpt T g h⟩

end Langlands.GroupScheme.SelfNormalizingAmbient
