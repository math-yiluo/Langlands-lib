import Langlands.Shimura.DefiniteFormsSmoothCoefficients
import Langlands.Shimura.DefiniteFormsHeckeExt

/-!
# Hecke operators on forms with coefficients and on their Ext

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, 1999, p.311,
Proposition 4.10, says that "as `K(N)^{ℓ,p}`-varies the spectral sequences are
`GG(𝔸_f^{ℓ,p})`-equivariant", for forms with coefficients in a representation `ρ` of `K_ℓ`. At a
fixed level `K` away from `p`, this equivariance is the action of the double-coset operators
`[K g L]` and of the Hecke algebra of `K`. This file constructs these operators on the forms of
level `e⁻¹ (1 × K)` with coefficients `ρ`, on their smooth parts, on `Ext^i(W, -)` of the smooth
parts, and on the intended abutment `Hom(X, A(K)[n])` with its filtration steps and graded
pieces. It shows that the maps of the presheaves of `DefiniteFormsSmoothCoefficients` along
arrows of levels are such operators. The operators and the Hecke algebra are the published
`LevelHecke.heckeOperator`, `LevelHeckeAlgebra` and `LevelHecke.heckeAct` of a representation of
the coefficient domain on the forms of trivial level with coefficients `ρ`. It does not show
that the differentials of the spectral sequence or the identification of its second page commute
with these operators, and does not treat the inverse systems over `m` or the Galois action.

## Main definitions

For groups `Γ`, `G` with `ι : Γ →* G`, an isomorphism of topological groups
`e : G ≃ₜ* H × H'`, a subgroup `D` of `G` and a representation `ρ` of `D`, in the namespace
`EquivariantForms`:

* `coefficientAwayTranslation R e ι ρ`: the action
  `(c • f) x = ρ (e⁻¹ (1, c)) (f (x * e⁻¹ (1, c)))` of the coefficient domain on the forms of
  trivial level with coefficients `ρ`; `coefficientAwayFixedEquiv` identifies its vectors fixed
  by `K'` with the forms of level `e⁻¹ (1 × K')`.
* `coefficientHecke R e ι ρ K L g`: the operator `[K g L]` from forms of level `e⁻¹ (1 × L)` to
  forms of level `e⁻¹ (1 × K)`,
  `([K g L] f) x = ∑ ρ (e⁻¹ (1, k g)) (f (x * e⁻¹ (1, k g)))` over representatives `k` of
  `K / (K ∩ g L g⁻¹)` (`coefficientHecke_apply_coe`); it commutes with right translation by `H`.
* `coefficientHeckeHom`, `coefficientSmoothHeckeHom`, `coefficientExtHecke`,
  `coefficientAbutmentHecke`, `coefficientFiltrationHecke`, `coefficientGradedHecke`: the
  operator `[K g L]` between the values at `L` and at `K` of `coefficientFormsPresheaf`,
  `coefficientSmoothPresheaf`, `coefficientExtPresheaf W i`, `coefficientAbutmentPresheaf X n`,
  `coefficientFiltrationPresheaf X n p` and `coefficientGradedPresheaf X n p`. The lemmas
  `coefficientFormsPresheaf_map_eq` and its analogues say that the map of each presheaf along an
  arrow `a : K ⟶ L` is `[K a L]` of its element.
* `coefficientFormsHeckeAlgebraHom`, `coefficientSmoothHeckeAlgebraHom`,
  `coefficientExtHeckeAlgebraHom`, `coefficientAbutmentHeckeAlgebraHom`,
  `coefficientFiltrationHeckeAlgebraHom`, `coefficientGradedHeckeAlgebraHom`: the Hecke algebra
  of `K` acting on the values at `K` of these presheaves, as ring homomorphisms to their
  endomorphisms; the element `doubleCoset K g` acts by `[K g K]`
  (`coefficientFormsHeckeAlgebraHom_doubleCoset` and its analogues).

In the namespace `DefiniteForms`, for `σ : AlgebraInvolution ℚ A`, a finite place `ℓ`, a
subgroup `Kℓ` of the `ℓ`-adic points, a representation `𝓛` of `Kℓ`, `p ≠ 0` and the published
splitting `σ.finiteAdelicPointsSplit p hp : GJ(𝔸_f) ≃ₜ* GJ(∏_{v ∣ p} ℚ_v) × GJ(𝔸_f^{(p)})`:
`dividingCoefficientSmoothHecke`, `dividingCoefficientExtHecke`,
`dividingCoefficientAbutmentHecke`, `dividingCoefficientFiltrationHecke`,
`dividingCoefficientGradedHecke` and the corresponding `*HeckeAlgebraHom`, for compact open
levels `K`, `L` of `dividingCoefficientDomain σ ℓ Kℓ p hp` and `g` in it.
-/

noncomputable section

namespace Langlands.Shimura.EquivariantForms

open CategoryTheory CategoryTheory.Limits Opposite DerivedCategory
open Langlands.Cohomology Langlands.Shimura.CompactOpenLevel Langlands.Shimura.LevelHecke

universe t uR uΓ uG uH uH' u w

section CoefficientTranslation

variable (R : Type uR) [CommRing R] {Γ : Type uΓ} {G : Type uG} {H : Type uH} {H' : Type uH'}
  [Group Γ] [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] [Group H']
  [TopologicalSpace H'] (e : G ≃ₜ* H × H') (ι : Γ →* G) {D : Subgroup G} {V : Type t}
  [AddCommGroup V] [Module R V] (ρ : Representation R D V)

/-- Every element of the coefficient domain conjugates the trivial subgroup into itself. -/
lemma conj_mem_bot (c : coefficientDomain e D) :
    ∀ k ∈ (⊥ : Subgroup (coefficientDomain e D)), c⁻¹ * k * c ∈ (⊥ : Subgroup _) := by
  intro k hk
  rw [Subgroup.mem_bot] at hk ⊢
  rw [hk, mul_one, inv_mul_cancel]

/-- The coefficient domain acts on the forms of trivial level with coefficients `ρ` by
`(c • f) x = ρ (e⁻¹ (1, c)) (f (x * e⁻¹ (1, c)))`: the accepted `coefficientTransport` along `c`
from the trivial level to itself. -/
def coefficientAwayTranslation :
    Representation R (coefficientDomain e D) (coefficientForms R e ι ρ ⊥) where
  toFun c := coefficientTransport R e ι ρ c (conj_mem_bot e c)
  map_one' := by
    ext f x
    change ρ ⟨awayHom e ((1 : coefficientDomain e D) : H'), _⟩
      (f.1 (x * awayHom e ((1 : coefficientDomain e D) : H'))) = f.1 x
    have h₁ : (⟨awayHom e ((1 : coefficientDomain e D) : H'),
        awayHom_mem_of_mem_coefficientDomain (1 : coefficientDomain e D).2⟩ : D) = 1 :=
      Subtype.ext (by simp)
    rw [h₁, map_one, Module.End.one_apply, OneMemClass.coe_one, map_one, mul_one]
  map_mul' c₁ c₂ := by
    ext f x
    change ρ ⟨awayHom e ((c₁ * c₂ : coefficientDomain e D) : H'), _⟩
        (f.1 (x * awayHom e ((c₁ * c₂ : coefficientDomain e D) : H'))) =
      ρ ⟨awayHom e (c₁ : H'), _⟩ (ρ ⟨awayHom e (c₂ : H'), _⟩
        (f.1 (x * awayHom e (c₁ : H') * awayHom e (c₂ : H'))))
    have h₂ : (⟨awayHom e ((c₁ * c₂ : coefficientDomain e D) : H'),
        awayHom_mem_of_mem_coefficientDomain (c₁ * c₂).2⟩ : D) =
        ⟨awayHom e (c₁ : H'), awayHom_mem_of_mem_coefficientDomain c₁.2⟩ *
        ⟨awayHom e (c₂ : H'), awayHom_mem_of_mem_coefficientDomain c₂.2⟩ :=
      Subtype.ext (by simp only [Subgroup.coe_mul, map_mul])
    rw [h₂, map_mul, Module.End.mul_apply, Subgroup.coe_mul, map_mul, mul_assoc]

@[simp]
lemma coefficientAwayTranslation_apply_coe (c : coefficientDomain e D)
    (f : coefficientForms R e ι ρ ⊥) (x : G) :
    (coefficientAwayTranslation R e ι ρ c f).1 x =
      ρ ⟨awayHom e c, awayHom_mem_of_mem_coefficientDomain c.2⟩ (f.1 (x * awayHom e c)) :=
  rfl

/-- Right translation by `h ∈ H` on the forms of trivial level with coefficients `ρ` commutes
with `coefficientAwayTranslation`, since the two factors commute. -/
def coefficientTranslationIntertwining (h : H) :
    (coefficientAwayTranslation R e ι ρ).IntertwiningMap (coefficientAwayTranslation R e ι ρ) where
  toLinearMap := coefficientTranslation R e ι ρ ⊥ h
  isIntertwining' c := by
    ext f x
    change ρ _ (f.1 (x * factorHom e h * awayHom e (c : H'))) =
      ρ _ (f.1 (x * awayHom e (c : H') * factorHom e h))
    rw [mul_assoc, mul_assoc, (factorHom_commute_awayHom e h c).eq]

/-- The vectors of `coefficientAwayTranslation` fixed by a subgroup `K'` of the coefficient
domain are the forms of level `e⁻¹ (1 × K')` with coefficients `ρ`, by the identity on
functions. -/
def coefficientAwayFixedEquiv (K' : Subgroup (coefficientDomain e D)) :
    fixedVectors (coefficientAwayTranslation R e ι ρ) K' ≃ₗ[R] coefficientForms R e ι ρ K' where
  toFun f := ⟨f.1.1, f.1.2.1, fun g k => by
      obtain ⟨a, ha, hak⟩ := (mem_awayLevel (e := e)).1 k.2
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 ha
      have h := congrArg (fun f' : coefficientForms R e ι ρ ⊥ => f'.1 g) (f.2 ⟨b, hb⟩)
      change ρ ⟨awayHom e (b : H'), awayHom_mem_of_mem_coefficientDomain b.2⟩
        (f.1.1 (g * awayHom e (b : H'))) = f.1.1 g at h
      have hd : (Subgroup.inclusion (awayLevel_domainLevel_le e K') k⁻¹ : D) =
          (⟨awayHom e (b : H'), awayHom_mem_of_mem_coefficientDomain b.2⟩ : D)⁻¹ :=
        Subtype.ext (by simp [← hak])
      change f.1.1 (g * k) = ρ (Subgroup.inclusion (awayLevel_domainLevel_le e K') k⁻¹) (f.1.1 g)
      rw [hd, ← h, Representation.inv_self_apply, ← hak]
      rfl⟩
  invFun f := ⟨⟨f.1, f.2.1, fun g k => by
      obtain ⟨a, ha, hak⟩ := (mem_awayLevel (e := e)).1 k.2
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 ha
      exact f.2.2 g ⟨k, hak ▸ awayHom_mem_awayLevel e (Subgroup.mem_map_of_mem _
        ((show (⊥ : Subgroup (coefficientDomain e D)) ≤ K' from bot_le) hb))⟩⟩,
    fun k => Subtype.ext (funext fun x => by
      change ρ ⟨awayHom e ((k : coefficientDomain e D) : H'), _⟩
        (f.1 (x * awayHom e ((k : coefficientDomain e D) : H'))) = f.1 x
      rw [f.2.2 x ⟨awayHom e ((k : coefficientDomain e D) : H'),
        awayHom_mem_awayLevel e (Subgroup.mem_map_of_mem _ k.2)⟩]
      exact ρ.self_inv_apply _ _)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
lemma coefficientAwayFixedEquiv_apply_coe (K' : Subgroup (coefficientDomain e D))
    (f : fixedVectors (coefficientAwayTranslation R e ι ρ) K') :
    (coefficientAwayFixedEquiv R e ι ρ K' f).1 = f.1.1 :=
  rfl

@[simp]
lemma coefficientAwayFixedEquiv_symm_apply_coe (K' : Subgroup (coefficientDomain e D))
    (f : coefficientForms R e ι ρ K') :
    ((coefficientAwayFixedEquiv R e ι ρ K').symm f).1.1 = f.1 :=
  rfl

end CoefficientTranslation

section CoefficientHecke

variable (R : Type uR) [CommRing R] {Γ : Type uΓ} {G : Type uG} {H : Type uH} {H' : Type uH'}
  [Group Γ] [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] [Group H']
  [TopologicalSpace H'] [IsTopologicalGroup H'] (e : G ≃ₜ* H × H') (ι : Γ →* G)
  {D : Subgroup G} {V : Type t} [AddCommGroup V] [Module R V] (ρ : Representation R D V)

/-- The double-coset operator `[K g L]` from forms of level `e⁻¹ (1 × L)` with coefficients `ρ`
to forms of level `e⁻¹ (1 × K)` with coefficients `ρ`, for compact open levels `K`, `L` of the
coefficient domain and `g` in it: the published `LevelHecke.heckeOperator` of
`coefficientAwayTranslation`, through `coefficientAwayFixedEquiv`. -/
def coefficientHecke (K L : CompactOpenLevel (coefficientDomain e D))
    (g : coefficientDomain e D) :
    coefficientForms R e ι ρ L.subgroup →ₗ[R] coefficientForms R e ι ρ K.subgroup :=
  (coefficientAwayFixedEquiv R e ι ρ K.subgroup).toLinearMap ∘ₗ
    LevelHecke.heckeOperator (coefficientAwayTranslation R e ι ρ) K L g ∘ₗ
      (coefficientAwayFixedEquiv R e ι ρ L.subgroup).symm.toLinearMap

/-- The formula `([K g L] f) x = ∑ ρ (e⁻¹ (1, k g)) (f (x * e⁻¹ (1, k g)))` over representatives
`k` of `K / (K ∩ g L g⁻¹)`. -/
lemma coefficientHecke_apply_coe (K L : CompactOpenLevel (coefficientDomain e D))
    (g : coefficientDomain e D) (f : coefficientForms R e ι ρ L.subgroup) (x : G) :
    (coefficientHecke R e ι ρ K L g f).1 x =
      ∑ q : HeckeCosets K L g,
        ρ ⟨awayHom e (((q.out : coefficientDomain e D) * g : coefficientDomain e D) : H'),
            awayHom_mem_of_mem_coefficientDomain ((q.out : coefficientDomain e D) * g).2⟩
          (f.1 (x * awayHom e (((q.out : coefficientDomain e D) * g : coefficientDomain e D) :
            H'))) := by
  change (LevelHecke.heckeOperator (coefficientAwayTranslation R e ι ρ) K L g
    ((coefficientAwayFixedEquiv R e ι ρ L.subgroup).symm f) : coefficientForms R e ι ρ ⊥).1 x = _
  rw [heckeOperator_apply_out, Submodule.coe_sum, Finset.sum_apply]
  rfl

/-- The double-coset operator commutes with right translation by the first factor `H`. -/
def coefficientHeckeIntertwining (K L : CompactOpenLevel (coefficientDomain e D))
    (g : coefficientDomain e D) :
    (coefficientTranslation R e ι ρ L.subgroup).IntertwiningMap
      (coefficientTranslation R e ι ρ K.subgroup) where
  toLinearMap := coefficientHecke R e ι ρ K L g
  isIntertwining' h := LinearMap.ext fun f =>
    congrArg (coefficientAwayFixedEquiv R e ι ρ K.subgroup)
      (LinearMap.congr_fun (fixedVectorsMap_heckeOperator K L g
        (coefficientTranslationIntertwining R e ι ρ h))
        ((coefficientAwayFixedEquiv R e ι ρ L.subgroup).symm f)).symm

/-- The double-coset operator `[K g L]` as a morphism of representations of `H` between the
values of `coefficientFormsPresheaf` at `L` and at `K`. -/
def coefficientHeckeHom (K L : CompactOpenLevel (coefficientDomain e D))
    (g : coefficientDomain e D) :
    (coefficientFormsPresheaf R e ι ρ).obj (op L) ⟶ (coefficientFormsPresheaf R e ι ρ).obj (op K) :=
  Rep.ofHom (coefficientHeckeIntertwining R e ι ρ K L g)

/-- If `g⁻¹ K g ⊆ L`, the operator `[K g L]` is `coefficientTransport` along `g`. -/
lemma coefficientHecke_eq_coefficientTransport {K L : CompactOpenLevel (coefficientDomain e D)}
    {g : coefficientDomain e D} (hg : ∀ k ∈ K.subgroup, g⁻¹ * k * g ∈ L.subgroup) :
    coefficientHecke R e ι ρ K L g = coefficientTransport R e ι ρ g hg := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  change ((LevelHecke.heckeOperator (coefficientAwayTranslation R e ι ρ) K L g
    ((coefficientAwayFixedEquiv R e ι ρ L.subgroup).symm f) : coefficientForms R e ι ρ ⊥) :
      G → V) = _
  rw [heckeOperator_eq_comp_translateFixed, LinearMap.comp_apply,
    heckeOperator_one_of_le _ (fun k hk => mem_conjLevel.mpr (hg k hk)),
    translateFixed_apply_coe]
  rfl

/-- The map of `coefficientFormsPresheaf` along an arrow `a : K ⟶ L` of levels is the
double-coset operator `[K a L]` of its element. -/
lemma coefficientFormsPresheaf_map_eq {K L : CompactOpenLevel (coefficientDomain e D)}
    (a : K ⟶ L) :
    (coefficientFormsPresheaf R e ι ρ).map a.op = coefficientHeckeHom R e ι ρ K L a.element := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun f => ?_))
  exact (LinearMap.congr_fun (coefficientHecke_eq_coefficientTransport R e ι ρ a.respects) f).symm

/-- The operator `[K 1 K]` is the identity. -/
lemma coefficientHeckeHom_self (K : CompactOpenLevel (coefficientDomain e D)) :
    coefficientHeckeHom R e ι ρ K K 1 = 𝟙 _ := by
  have h := coefficientFormsPresheaf_map_eq R e ι ρ (𝟙 K)
  rw [op_id, CategoryTheory.Functor.map_id] at h
  exact h.symm

/-- The action `a • f` of an element `a` of the Hecke algebra of `K` on the forms of level
`e⁻¹ (1 × K)` with coefficients `ρ`: the published `LevelHecke.heckeAct` of
`coefficientAwayTranslation`, through `coefficientAwayFixedEquiv`. -/
def coefficientHeckeAct (K : CompactOpenLevel (coefficientDomain e D))
    (a : LevelHeckeAlgebra R K.subgroup) :
    coefficientForms R e ι ρ K.subgroup →ₗ[R] coefficientForms R e ι ρ K.subgroup :=
  (coefficientAwayFixedEquiv R e ι ρ K.subgroup).toLinearMap ∘ₗ
    heckeAct (coefficientAwayTranslation R e ι ρ) K.subgroup K.subgroup a ∘ₗ
      (coefficientAwayFixedEquiv R e ι ρ K.subgroup).symm.toLinearMap

/-- The action of the Hecke algebra commutes with right translation by the first factor `H`. -/
def coefficientHeckeActIntertwining (K : CompactOpenLevel (coefficientDomain e D))
    (a : LevelHeckeAlgebra R K.subgroup) :
    (coefficientTranslation R e ι ρ K.subgroup).IntertwiningMap
      (coefficientTranslation R e ι ρ K.subgroup) where
  toLinearMap := coefficientHeckeAct R e ι ρ K a
  isIntertwining' h := LinearMap.ext fun f =>
    congrArg (coefficientAwayFixedEquiv R e ι ρ K.subgroup)
      (fixedVectorsMap_heckeAct (coefficientTranslationIntertwining R e ι ρ h) K.subgroup
        K.subgroup a ((coefficientAwayFixedEquiv R e ι ρ K.subgroup).symm f)).symm

/-- The Hecke algebra of `K` acting on the value of `coefficientFormsPresheaf` at `K`, as a ring
homomorphism to its endomorphisms as a representation of `H`. -/
def coefficientFormsHeckeAlgebraHom (K : CompactOpenLevel (coefficientDomain e D)) :
    LevelHeckeAlgebra R K.subgroup →+* End ((coefficientFormsPresheaf R e ι ρ).obj (op K)) where
  toFun a := Rep.ofHom (coefficientHeckeActIntertwining R e ι ρ K a)
  map_one' := by
    refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun f => ?_))
    exact congrArg (coefficientAwayFixedEquiv R e ι ρ K.subgroup)
      (one_smul (LevelHeckeAlgebra R K.subgroup)
        ((coefficientAwayFixedEquiv R e ι ρ K.subgroup).symm f))
  map_mul' a b := by
    refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun f => ?_))
    exact congrArg (coefficientAwayFixedEquiv R e ι ρ K.subgroup)
      (mul_smul a b ((coefficientAwayFixedEquiv R e ι ρ K.subgroup).symm f))
  map_zero' := by
    refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun f => ?_))
    exact congrArg (coefficientAwayFixedEquiv R e ι ρ K.subgroup)
      (zero_smul (LevelHeckeAlgebra R K.subgroup)
        ((coefficientAwayFixedEquiv R e ι ρ K.subgroup).symm f))
  map_add' a b := by
    refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun f => ?_))
    exact congrArg (coefficientAwayFixedEquiv R e ι ρ K.subgroup)
      (add_smul a b ((coefficientAwayFixedEquiv R e ι ρ K.subgroup).symm f))

/-- The element `[K g K]` of the Hecke algebra acts by the double-coset operator. -/
lemma coefficientFormsHeckeAlgebraHom_doubleCoset (K : CompactOpenLevel (coefficientDomain e D))
    (g : coefficientDomain e D) :
    coefficientFormsHeckeAlgebraHom R e ι ρ K (doubleCoset K g) =
      coefficientHeckeHom R e ι ρ K K g := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun f => ?_))
  exact congrArg (coefficientAwayFixedEquiv R e ι ρ K.subgroup)
    (doubleCoset_smul (coefficientAwayTranslation R e ι ρ) K g
      ((coefficientAwayFixedEquiv R e ι ρ K.subgroup).symm f))

end CoefficientHecke

section CoefficientHeckeSmooth

variable (R : Type uR) [CommRing R] {Γ : Type uΓ} {G : Type uG} {H : Type uH} {H' : Type uH'}
  [Group Γ] [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Group H'] [TopologicalSpace H'] [IsTopologicalGroup H'] (e : G ≃ₜ* H × H') (ι : Γ →* G)
  {D : Subgroup G} {V : Type t} [AddCommGroup V] [Module R V] (ρ : Representation R D V)

/-- The double-coset operator `[K g L]` on the smooth parts: a morphism of smooth
representations of `H` between the values of `coefficientSmoothPresheaf` at `L` and at `K`. -/
def coefficientSmoothHeckeHom (K L : CompactOpenLevel (coefficientDomain e D))
    (g : coefficientDomain e D) :
    (coefficientSmoothPresheaf R e ι ρ).obj (op L) ⟶
      (coefficientSmoothPresheaf R e ι ρ).obj (op K) :=
  (SmoothRep.smoothPartFunctor.{uR, uH, max uG t} R H).map (coefficientHeckeHom R e ι ρ K L g)

/-- The map of `coefficientSmoothPresheaf` along an arrow `a : K ⟶ L` of levels is the
double-coset operator `[K a L]` of its element. -/
lemma coefficientSmoothPresheaf_map_eq {K L : CompactOpenLevel (coefficientDomain e D)}
    (a : K ⟶ L) :
    (coefficientSmoothPresheaf R e ι ρ).map a.op =
      coefficientSmoothHeckeHom R e ι ρ K L a.element := by
  change (SmoothRep.smoothPartFunctor.{uR, uH, max uG t} R H).map
    ((coefficientFormsPresheaf R e ι ρ).map a.op) = _
  rw [coefficientFormsPresheaf_map_eq]
  rfl

/-- The Hecke algebra of `K` acting on the value of `coefficientSmoothPresheaf` at `K`, as a ring
homomorphism to its endomorphisms as a smooth representation of `H`. -/
def coefficientSmoothHeckeAlgebraHom (K : CompactOpenLevel (coefficientDomain e D)) :
    LevelHeckeAlgebra R K.subgroup →+* End ((coefficientSmoothPresheaf R e ι ρ).obj (op K)) :=
  (endRingHom (SmoothRep.smoothPartFunctor.{uR, uH, max uG t} R H) _).comp
    (coefficientFormsHeckeAlgebraHom R e ι ρ K)

/-- The element `[K g K]` of the Hecke algebra acts by the double-coset operator. -/
lemma coefficientSmoothHeckeAlgebraHom_doubleCoset (K : CompactOpenLevel (coefficientDomain e D))
    (g : coefficientDomain e D) :
    coefficientSmoothHeckeAlgebraHom R e ι ρ K (doubleCoset K g) =
      coefficientSmoothHeckeHom R e ι ρ K K g := by
  change (SmoothRep.smoothPartFunctor.{uR, uH, max uG t} R H).map
    (coefficientFormsHeckeAlgebraHom R e ι ρ K (doubleCoset K g)) = _
  rw [coefficientFormsHeckeAlgebraHom_doubleCoset]
  rfl

end CoefficientHeckeSmooth

section CoefficientHeckeExt

variable (R : Type u) [CommRing R] {Γ : Type uΓ} {G : Type u} {H : Type u} {H' : Type uH'}
  [Group Γ] [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Group H'] [TopologicalSpace H'] [IsTopologicalGroup H'] (e : G ≃ₜ* H × H') (ι : Γ →* G)
  {D : Subgroup G} {V : Type u} [AddCommGroup V] [Module R V] (ρ : Representation R D V)

/-- The double-coset operator `[K g L]` on `Ext^i(W, -)` of the smooth forms with coefficients
`ρ`: the map from the value of `coefficientExtPresheaf W i` at `L` to its value at `K`. -/
def coefficientExtHecke (W : SmoothRep.{u, u, u} R H) (i : ℕ)
    (K L : CompactOpenLevel (coefficientDomain e D)) (g : coefficientDomain e D) :
    (coefficientExtPresheaf R e ι ρ W i).obj (op L) ⟶
      (coefficientExtPresheaf R e ι ρ W i).obj (op K) :=
  (SmoothExt.ext R H W i).map (coefficientSmoothHeckeHom R e ι ρ K L g)

/-- The map of `coefficientExtPresheaf W i` along an arrow `a : K ⟶ L` of levels is the
double-coset operator `[K a L]` of its element. -/
lemma coefficientExtPresheaf_map_eq (W : SmoothRep.{u, u, u} R H) (i : ℕ)
    {K L : CompactOpenLevel (coefficientDomain e D)} (a : K ⟶ L) :
    (coefficientExtPresheaf R e ι ρ W i).map a.op =
      coefficientExtHecke R e ι ρ W i K L a.element := by
  change (SmoothExt.ext R H W i).map ((coefficientSmoothPresheaf R e ι ρ).map a.op) = _
  rw [coefficientSmoothPresheaf_map_eq]
  rfl

/-- The Hecke algebra of `K` acting on `Ext^i(W, -)` of the smooth forms of level
`e⁻¹ (1 × K)` with coefficients `ρ`, as a ring homomorphism to the `R`-linear endomorphisms. -/
def coefficientExtHeckeAlgebraHom (W : SmoothRep.{u, u, u} R H) (i : ℕ)
    (K : CompactOpenLevel (coefficientDomain e D)) :
    LevelHeckeAlgebra R K.subgroup →+* End ((coefficientExtPresheaf R e ι ρ W i).obj (op K)) :=
  (endRingHom (SmoothExt.ext R H W i) _).comp (coefficientSmoothHeckeAlgebraHom R e ι ρ K)

/-- The element `[K g K]` of the Hecke algebra acts on `Ext^i` by the double-coset operator. -/
lemma coefficientExtHeckeAlgebraHom_doubleCoset (W : SmoothRep.{u, u, u} R H) (i : ℕ)
    (K : CompactOpenLevel (coefficientDomain e D)) (g : coefficientDomain e D) :
    coefficientExtHeckeAlgebraHom R e ι ρ W i K (doubleCoset K g) =
      coefficientExtHecke R e ι ρ W i K K g := by
  change (SmoothExt.ext R H W i).map
    (coefficientSmoothHeckeAlgebraHom R e ι ρ K (doubleCoset K g)) = _
  rw [coefficientSmoothHeckeAlgebraHom_doubleCoset]
  rfl

end CoefficientHeckeExt

section CoefficientHeckeAbutment

variable (R : Type u) [CommRing R] {Γ : Type uΓ} {G : Type u} {H : Type u} {H' : Type uH'}
  [Group Γ] [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Group H'] [TopologicalSpace H'] [IsTopologicalGroup H'] (e : G ≃ₜ* H × H') (ι : Γ →* G)
  {D : Subgroup G} {V : Type u} [AddCommGroup V] [Module R V] (ρ : Representation R D V)
  [HasDerivedCategory.{w} (SmoothRep.{u, u, u} R H)]

/-- The double-coset operator `[K g L]` on the abutment `Hom(X, A(-)[n])` of forms with
coefficients `ρ`, by postcomposition. -/
def coefficientAbutmentHecke (X : DerivedCategory (SmoothRep.{u, u, u} R H)) (n : ℤ)
    (K L : CompactOpenLevel (coefficientDomain e D)) (g : coefficientDomain e D) :
    (coefficientAbutmentPresheaf R e ι ρ X n).obj (op L) ⟶
      (coefficientAbutmentPresheaf R e ι ρ X n).obj (op K) :=
  (singleFunctor (SmoothRep.{u, u, u} R H) 0 ⋙ shiftFunctor _ n ⋙
    preadditiveCoyoneda.obj (op X)).map (coefficientSmoothHeckeHom R e ι ρ K L g)

/-- The map of `coefficientAbutmentPresheaf X n` along an arrow `a : K ⟶ L` of levels is the
double-coset operator `[K a L]` of its element. -/
lemma coefficientAbutmentPresheaf_map_eq (X : DerivedCategory (SmoothRep.{u, u, u} R H)) (n : ℤ)
    {K L : CompactOpenLevel (coefficientDomain e D)} (a : K ⟶ L) :
    (coefficientAbutmentPresheaf R e ι ρ X n).map a.op =
      coefficientAbutmentHecke R e ι ρ X n K L a.element := by
  change (singleFunctor (SmoothRep.{u, u, u} R H) 0 ⋙ shiftFunctor _ n ⋙
    preadditiveCoyoneda.obj (op X)).map ((coefficientSmoothPresheaf R e ι ρ).map a.op) = _
  rw [coefficientSmoothPresheaf_map_eq]
  rfl

/-- The Hecke algebra of `K` acting on the abutment `Hom(X, A(K)[n])` of forms with coefficients
`ρ` by postcomposition, as a ring homomorphism to its additive endomorphisms. -/
def coefficientAbutmentHeckeAlgebraHom (X : DerivedCategory (SmoothRep.{u, u, u} R H)) (n : ℤ)
    (K : CompactOpenLevel (coefficientDomain e D)) :
    LevelHeckeAlgebra R K.subgroup →+*
      End ((coefficientAbutmentPresheaf R e ι ρ X n).obj (op K)) :=
  (endRingHom (singleFunctor (SmoothRep.{u, u, u} R H) 0 ⋙ shiftFunctor _ n ⋙
    preadditiveCoyoneda.obj (op X)) _).comp (coefficientSmoothHeckeAlgebraHom R e ι ρ K)

/-- The element `[K g K]` of the Hecke algebra acts on the abutment by the double-coset
operator. -/
lemma coefficientAbutmentHeckeAlgebraHom_doubleCoset
    (X : DerivedCategory (SmoothRep.{u, u, u} R H)) (n : ℤ)
    (K : CompactOpenLevel (coefficientDomain e D)) (g : coefficientDomain e D) :
    coefficientAbutmentHeckeAlgebraHom R e ι ρ X n K (doubleCoset K g) =
      coefficientAbutmentHecke R e ι ρ X n K K g := by
  change (singleFunctor (SmoothRep.{u, u, u} R H) 0 ⋙ shiftFunctor _ n ⋙
    preadditiveCoyoneda.obj (op X)).map
      (coefficientSmoothHeckeAlgebraHom R e ι ρ K (doubleCoset K g)) = _
  rw [coefficientSmoothHeckeAlgebraHom_doubleCoset]
  rfl

/-- The double-coset operator `[K g L]` on the step `F^p` of the abutment filtration, by
postcomposition. -/
def coefficientFiltrationHecke (X : DerivedCategory (SmoothRep.{u, u, u} R H)) (n p : ℤ)
    (K L : CompactOpenLevel (coefficientDomain e D)) (g : coefficientDomain e D) :
    (coefficientFiltrationPresheaf R e ι ρ X n p).obj (op L) ⟶
      (coefficientFiltrationPresheaf R e ι ρ X n p).obj (op K) :=
  (singleFunctor (SmoothRep.{u, u, u} R H) 0 ⋙
    HyperextAbutment.filtrationFunctor TStructure.t X n p).map
      (coefficientSmoothHeckeHom R e ι ρ K L g)

/-- The map of `coefficientFiltrationPresheaf X n p` along an arrow `a : K ⟶ L` of levels is the
double-coset operator `[K a L]` of its element. -/
lemma coefficientFiltrationPresheaf_map_eq (X : DerivedCategory (SmoothRep.{u, u, u} R H))
    (n p : ℤ) {K L : CompactOpenLevel (coefficientDomain e D)} (a : K ⟶ L) :
    (coefficientFiltrationPresheaf R e ι ρ X n p).map a.op =
      coefficientFiltrationHecke R e ι ρ X n p K L a.element := by
  change AddCommGrpCat.ofHom (HyperextAbutment.filtrationPostcomp TStructure.t X
    ((singleFunctor _ 0).map ((coefficientSmoothPresheaf R e ι ρ).map a.op)) n p) = _
  rw [coefficientSmoothPresheaf_map_eq]
  rfl

/-- The inclusion `F^p ⊆ Hom(X, A(-)[n])` commutes with the double-coset operators. -/
lemma coefficientFiltrationHecke_comp_filtrationι
    (X : DerivedCategory (SmoothRep.{u, u, u} R H)) (n p : ℤ)
    (K L : CompactOpenLevel (coefficientDomain e D)) (g : coefficientDomain e D) :
    coefficientFiltrationHecke R e ι ρ X n p K L g ≫
        (HyperextAbutment.filtrationι TStructure.t X n p).app
          ((singleFunctor _ 0).obj ((coefficientSmoothPresheaf R e ι ρ).obj (op K))) =
      (HyperextAbutment.filtrationι TStructure.t X n p).app
          ((singleFunctor _ 0).obj ((coefficientSmoothPresheaf R e ι ρ).obj (op L))) ≫
        coefficientAbutmentHecke R e ι ρ X n K L g :=
  (HyperextAbutment.filtrationι TStructure.t X n p).naturality _

/-- The Hecke algebra of `K` acting on the step `F^p` of the abutment filtration on
`Hom(X, A(K)[n])`, as a ring homomorphism to its additive endomorphisms. -/
def coefficientFiltrationHeckeAlgebraHom (X : DerivedCategory (SmoothRep.{u, u, u} R H))
    (n p : ℤ) (K : CompactOpenLevel (coefficientDomain e D)) :
    LevelHeckeAlgebra R K.subgroup →+*
      End ((coefficientFiltrationPresheaf R e ι ρ X n p).obj (op K)) :=
  (endRingHom (singleFunctor (SmoothRep.{u, u, u} R H) 0 ⋙
    HyperextAbutment.filtrationFunctor TStructure.t X n p) _).comp
      (coefficientSmoothHeckeAlgebraHom R e ι ρ K)

/-- The element `[K g K]` of the Hecke algebra acts on the filtration step `F^p` by the
double-coset operator. -/
lemma coefficientFiltrationHeckeAlgebraHom_doubleCoset
    (X : DerivedCategory (SmoothRep.{u, u, u} R H)) (n p : ℤ)
    (K : CompactOpenLevel (coefficientDomain e D)) (g : coefficientDomain e D) :
    coefficientFiltrationHeckeAlgebraHom R e ι ρ X n p K (doubleCoset K g) =
      coefficientFiltrationHecke R e ι ρ X n p K K g := by
  change (singleFunctor (SmoothRep.{u, u, u} R H) 0 ⋙
    HyperextAbutment.filtrationFunctor TStructure.t X n p).map
      (coefficientSmoothHeckeAlgebraHom R e ι ρ K (doubleCoset K g)) = _
  rw [coefficientSmoothHeckeAlgebraHom_doubleCoset]
  rfl

/-- The double-coset operator `[K g L]` on the graded piece `gr^p` of the abutment filtration,
by postcomposition. -/
def coefficientGradedHecke (X : DerivedCategory (SmoothRep.{u, u, u} R H)) (n p : ℤ)
    (K L : CompactOpenLevel (coefficientDomain e D)) (g : coefficientDomain e D) :
    (coefficientGradedPresheaf R e ι ρ X n p).obj (op L) ⟶
      (coefficientGradedPresheaf R e ι ρ X n p).obj (op K) :=
  (singleFunctor (SmoothRep.{u, u, u} R H) 0 ⋙
    HyperextAbutment.gradedFunctor TStructure.t X n p).map
      (coefficientSmoothHeckeHom R e ι ρ K L g)

/-- The map of `coefficientGradedPresheaf X n p` along an arrow `a : K ⟶ L` of levels is the
double-coset operator `[K a L]` of its element. -/
lemma coefficientGradedPresheaf_map_eq (X : DerivedCategory (SmoothRep.{u, u, u} R H))
    (n p : ℤ) {K L : CompactOpenLevel (coefficientDomain e D)} (a : K ⟶ L) :
    (coefficientGradedPresheaf R e ι ρ X n p).map a.op =
      coefficientGradedHecke R e ι ρ X n p K L a.element := by
  change AddCommGrpCat.ofHom (HyperextAbutment.gradedPostcomp TStructure.t X
    ((singleFunctor _ 0).map ((coefficientSmoothPresheaf R e ι ρ).map a.op)) n p) = _
  rw [coefficientSmoothPresheaf_map_eq]
  rfl

/-- The projection `F^p ⟶ gr^p` commutes with the double-coset operators. -/
lemma coefficientFiltrationHecke_comp_gradedπ (X : DerivedCategory (SmoothRep.{u, u, u} R H))
    (n p : ℤ) (K L : CompactOpenLevel (coefficientDomain e D)) (g : coefficientDomain e D) :
    coefficientFiltrationHecke R e ι ρ X n p K L g ≫
        (HyperextAbutment.gradedπ TStructure.t X n p).app
          ((singleFunctor _ 0).obj ((coefficientSmoothPresheaf R e ι ρ).obj (op K))) =
      (HyperextAbutment.gradedπ TStructure.t X n p).app
          ((singleFunctor _ 0).obj ((coefficientSmoothPresheaf R e ι ρ).obj (op L))) ≫
        coefficientGradedHecke R e ι ρ X n p K L g :=
  (HyperextAbutment.gradedπ TStructure.t X n p).naturality _

/-- The Hecke algebra of `K` acting on the graded piece `gr^p` of the abutment filtration on
`Hom(X, A(K)[n])`, as a ring homomorphism to its additive endomorphisms. -/
def coefficientGradedHeckeAlgebraHom (X : DerivedCategory (SmoothRep.{u, u, u} R H))
    (n p : ℤ) (K : CompactOpenLevel (coefficientDomain e D)) :
    LevelHeckeAlgebra R K.subgroup →+*
      End ((coefficientGradedPresheaf R e ι ρ X n p).obj (op K)) :=
  (endRingHom (singleFunctor (SmoothRep.{u, u, u} R H) 0 ⋙
    HyperextAbutment.gradedFunctor TStructure.t X n p) _).comp
      (coefficientSmoothHeckeAlgebraHom R e ι ρ K)

/-- The element `[K g K]` of the Hecke algebra acts on the graded piece `gr^p` by the
double-coset operator. -/
lemma coefficientGradedHeckeAlgebraHom_doubleCoset
    (X : DerivedCategory (SmoothRep.{u, u, u} R H)) (n p : ℤ)
    (K : CompactOpenLevel (coefficientDomain e D)) (g : coefficientDomain e D) :
    coefficientGradedHeckeAlgebraHom R e ι ρ X n p K (doubleCoset K g) =
      coefficientGradedHecke R e ι ρ X n p K K g := by
  change (singleFunctor (SmoothRep.{u, u, u} R H) 0 ⋙
    HyperextAbutment.gradedFunctor TStructure.t X n p).map
      (coefficientSmoothHeckeAlgebraHom R e ι ρ K (doubleCoset K g)) = _
  rw [coefficientSmoothHeckeAlgebraHom_doubleCoset]
  rfl

end CoefficientHeckeAbutment

end Langlands.Shimura.EquivariantForms

namespace Langlands.Shimura.DefiniteForms

open CategoryTheory Opposite DerivedCategory
open Langlands.Global Langlands.Cohomology Langlands.Shimura.EquivariantForms
open Langlands.Shimura.LevelHecke

universe u w

variable {A : Type u} [Ring A] [Algebra ℚ A] (σ : AlgebraInvolution ℚ A) [Module.Finite ℚ A]
  (ℓ : FinitePlace ℚ) (Kℓ : Subgroup (σ.Points (FiniteCompletion ℚ ℓ))) {R : Type u} [CommRing R]
  {V : Type u} [AddCommGroup V] [Module R V] (𝓛 : Representation R Kℓ V) (p : ℕ) (hp : p ≠ 0)

/-- The double-coset operator `[K g L]`, for compact open levels `K`, `L` of
`dividingCoefficientDomain σ ℓ Kℓ p hp` and `g` in it, between the values of
`dividingCoefficientSmoothPresheaf` at `L` and at `K`, as a morphism of smooth representations
of `GJ(∏_{v ∣ p} ℚ_v)`. -/
def dividingCoefficientSmoothHecke (K L : CompactOpenLevel (dividingCoefficientDomain σ ℓ Kℓ p hp))
    (g : dividingCoefficientDomain σ ℓ Kℓ p hp) :
    (dividingCoefficientSmoothPresheaf σ ℓ Kℓ 𝓛 p hp).obj (op L) ⟶
      (dividingCoefficientSmoothPresheaf σ ℓ Kℓ 𝓛 p hp).obj (op K) :=
  coefficientSmoothHeckeHom R (σ.finiteAdelicPointsSplit p hp) σ.finiteAdelicDiagonal
    (localCoefficientRep σ ℓ Kℓ 𝓛) K L g

/-- The map of `dividingCoefficientSmoothPresheaf` along an arrow `a : K ⟶ L` of levels is the
double-coset operator `[K a L]` of its element. -/
lemma dividingCoefficientSmoothPresheaf_map_eq
    {K L : CompactOpenLevel (dividingCoefficientDomain σ ℓ Kℓ p hp)} (a : K ⟶ L) :
    (dividingCoefficientSmoothPresheaf σ ℓ Kℓ 𝓛 p hp).map a.op =
      dividingCoefficientSmoothHecke σ ℓ Kℓ 𝓛 p hp K L a.element :=
  coefficientSmoothPresheaf_map_eq R _ _ _ a

/-- The Hecke algebra of a compact open level `K` of `dividingCoefficientDomain σ ℓ Kℓ p hp`
acting on the value of `dividingCoefficientSmoothPresheaf` at `K`, as a ring homomorphism to its
endomorphisms as a smooth representation of `GJ(∏_{v ∣ p} ℚ_v)`. -/
def dividingCoefficientSmoothHeckeAlgebraHom
    (K : CompactOpenLevel (dividingCoefficientDomain σ ℓ Kℓ p hp)) :
    LevelHeckeAlgebra R K.subgroup →+*
      End ((dividingCoefficientSmoothPresheaf σ ℓ Kℓ 𝓛 p hp).obj (op K)) :=
  coefficientSmoothHeckeAlgebraHom R (σ.finiteAdelicPointsSplit p hp) σ.finiteAdelicDiagonal
    (localCoefficientRep σ ℓ Kℓ 𝓛) K

/-- The element `[K g K]` of the Hecke algebra acts by the double-coset operator. -/
lemma dividingCoefficientSmoothHeckeAlgebraHom_doubleCoset
    (K : CompactOpenLevel (dividingCoefficientDomain σ ℓ Kℓ p hp))
    (g : dividingCoefficientDomain σ ℓ Kℓ p hp) :
    dividingCoefficientSmoothHeckeAlgebraHom σ ℓ Kℓ 𝓛 p hp K (doubleCoset K g) =
      dividingCoefficientSmoothHecke σ ℓ Kℓ 𝓛 p hp K K g :=
  coefficientSmoothHeckeAlgebraHom_doubleCoset R _ _ _ K g

/-- The double-coset operator `[K g L]` on `Ext^i(W, -)` of the forms of
`dividingCoefficientSmoothPresheaf`: the map from the value of
`dividingCoefficientExtPresheaf W i` at `L` to its value at `K`. -/
def dividingCoefficientExtHecke (W : SmoothRep.{u, u, u} R (σ.DividingPoints p)) (i : ℕ)
    (K L : CompactOpenLevel (dividingCoefficientDomain σ ℓ Kℓ p hp))
    (g : dividingCoefficientDomain σ ℓ Kℓ p hp) :
    (dividingCoefficientExtPresheaf σ ℓ Kℓ 𝓛 p hp W i).obj (op L) ⟶
      (dividingCoefficientExtPresheaf σ ℓ Kℓ 𝓛 p hp W i).obj (op K) :=
  coefficientExtHecke R (σ.finiteAdelicPointsSplit p hp) σ.finiteAdelicDiagonal
    (localCoefficientRep σ ℓ Kℓ 𝓛) W i K L g

/-- The map of `dividingCoefficientExtPresheaf W i` along an arrow `a : K ⟶ L` of levels is the
double-coset operator `[K a L]` of its element. -/
lemma dividingCoefficientExtPresheaf_map_eq (W : SmoothRep.{u, u, u} R (σ.DividingPoints p))
    (i : ℕ) {K L : CompactOpenLevel (dividingCoefficientDomain σ ℓ Kℓ p hp)} (a : K ⟶ L) :
    (dividingCoefficientExtPresheaf σ ℓ Kℓ 𝓛 p hp W i).map a.op =
      dividingCoefficientExtHecke σ ℓ Kℓ 𝓛 p hp W i K L a.element :=
  coefficientExtPresheaf_map_eq R _ _ _ W i a

/-- The Hecke algebra of a compact open level `K` of `dividingCoefficientDomain σ ℓ Kℓ p hp`
acting on `Ext^i(W, -)` of the forms of `dividingCoefficientSmoothPresheaf` at `K`, as a ring
homomorphism to the `R`-linear endomorphisms. -/
def dividingCoefficientExtHeckeAlgebraHom (W : SmoothRep.{u, u, u} R (σ.DividingPoints p))
    (i : ℕ) (K : CompactOpenLevel (dividingCoefficientDomain σ ℓ Kℓ p hp)) :
    LevelHeckeAlgebra R K.subgroup →+*
      End ((dividingCoefficientExtPresheaf σ ℓ Kℓ 𝓛 p hp W i).obj (op K)) :=
  coefficientExtHeckeAlgebraHom R (σ.finiteAdelicPointsSplit p hp) σ.finiteAdelicDiagonal
    (localCoefficientRep σ ℓ Kℓ 𝓛) W i K

/-- The element `[K g K]` of the Hecke algebra acts on `Ext^i` by the double-coset operator. -/
lemma dividingCoefficientExtHeckeAlgebraHom_doubleCoset
    (W : SmoothRep.{u, u, u} R (σ.DividingPoints p)) (i : ℕ)
    (K : CompactOpenLevel (dividingCoefficientDomain σ ℓ Kℓ p hp))
    (g : dividingCoefficientDomain σ ℓ Kℓ p hp) :
    dividingCoefficientExtHeckeAlgebraHom σ ℓ Kℓ 𝓛 p hp W i K (doubleCoset K g) =
      dividingCoefficientExtHecke σ ℓ Kℓ 𝓛 p hp W i K K g :=
  coefficientExtHeckeAlgebraHom_doubleCoset R _ _ _ W i K g

variable [HasDerivedCategory.{w} (SmoothRep.{u, u, u} R (σ.DividingPoints p))]

/-- The double-coset operator `[K g L]` on the abutment `Hom(X, A(-)[n])` of
`dividingCoefficientSpectralSequence`, by postcomposition. -/
def dividingCoefficientAbutmentHecke
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n : ℤ)
    (K L : CompactOpenLevel (dividingCoefficientDomain σ ℓ Kℓ p hp))
    (g : dividingCoefficientDomain σ ℓ Kℓ p hp) :
    (dividingCoefficientAbutmentPresheaf σ ℓ Kℓ 𝓛 p hp X n).obj (op L) ⟶
      (dividingCoefficientAbutmentPresheaf σ ℓ Kℓ 𝓛 p hp X n).obj (op K) :=
  coefficientAbutmentHecke R (σ.finiteAdelicPointsSplit p hp) σ.finiteAdelicDiagonal
    (localCoefficientRep σ ℓ Kℓ 𝓛) X n K L g

/-- The map of `dividingCoefficientAbutmentPresheaf X n` along an arrow `a : K ⟶ L` of levels is
the double-coset operator `[K a L]` of its element. -/
lemma dividingCoefficientAbutmentPresheaf_map_eq
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n : ℤ)
    {K L : CompactOpenLevel (dividingCoefficientDomain σ ℓ Kℓ p hp)} (a : K ⟶ L) :
    (dividingCoefficientAbutmentPresheaf σ ℓ Kℓ 𝓛 p hp X n).map a.op =
      dividingCoefficientAbutmentHecke σ ℓ Kℓ 𝓛 p hp X n K L a.element :=
  coefficientAbutmentPresheaf_map_eq R _ _ _ X n a

/-- The Hecke algebra of a compact open level `K` of `dividingCoefficientDomain σ ℓ Kℓ p hp`
acting on the abutment `Hom(X, A(K)[n])` by postcomposition. -/
def dividingCoefficientAbutmentHeckeAlgebraHom
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n : ℤ)
    (K : CompactOpenLevel (dividingCoefficientDomain σ ℓ Kℓ p hp)) :
    LevelHeckeAlgebra R K.subgroup →+*
      End ((dividingCoefficientAbutmentPresheaf σ ℓ Kℓ 𝓛 p hp X n).obj (op K)) :=
  coefficientAbutmentHeckeAlgebraHom R (σ.finiteAdelicPointsSplit p hp) σ.finiteAdelicDiagonal
    (localCoefficientRep σ ℓ Kℓ 𝓛) X n K

/-- The double-coset operator `[K g L]` on the step `F^i` of the abutment filtration of
`dividingCoefficientSpectralSequence`, by postcomposition. -/
def dividingCoefficientFiltrationHecke
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n i : ℤ)
    (K L : CompactOpenLevel (dividingCoefficientDomain σ ℓ Kℓ p hp))
    (g : dividingCoefficientDomain σ ℓ Kℓ p hp) :
    (dividingCoefficientFiltrationPresheaf σ ℓ Kℓ 𝓛 p hp X n i).obj (op L) ⟶
      (dividingCoefficientFiltrationPresheaf σ ℓ Kℓ 𝓛 p hp X n i).obj (op K) :=
  coefficientFiltrationHecke R (σ.finiteAdelicPointsSplit p hp) σ.finiteAdelicDiagonal
    (localCoefficientRep σ ℓ Kℓ 𝓛) X n i K L g

/-- The map of `dividingCoefficientFiltrationPresheaf X n i` along an arrow `a : K ⟶ L` of
levels is the double-coset operator `[K a L]` of its element. -/
lemma dividingCoefficientFiltrationPresheaf_map_eq
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n i : ℤ)
    {K L : CompactOpenLevel (dividingCoefficientDomain σ ℓ Kℓ p hp)} (a : K ⟶ L) :
    (dividingCoefficientFiltrationPresheaf σ ℓ Kℓ 𝓛 p hp X n i).map a.op =
      dividingCoefficientFiltrationHecke σ ℓ Kℓ 𝓛 p hp X n i K L a.element :=
  coefficientFiltrationPresheaf_map_eq R _ _ _ X n i a

/-- The Hecke algebra of a compact open level `K` of `dividingCoefficientDomain σ ℓ Kℓ p hp`
acting on the step `F^i` of the abutment filtration on `Hom(X, A(K)[n])`. -/
def dividingCoefficientFiltrationHeckeAlgebraHom
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n i : ℤ)
    (K : CompactOpenLevel (dividingCoefficientDomain σ ℓ Kℓ p hp)) :
    LevelHeckeAlgebra R K.subgroup →+*
      End ((dividingCoefficientFiltrationPresheaf σ ℓ Kℓ 𝓛 p hp X n i).obj (op K)) :=
  coefficientFiltrationHeckeAlgebraHom R (σ.finiteAdelicPointsSplit p hp)
    σ.finiteAdelicDiagonal (localCoefficientRep σ ℓ Kℓ 𝓛) X n i K

/-- The double-coset operator `[K g L]` on the graded piece `gr^i` of the abutment filtration of
`dividingCoefficientSpectralSequence`, by postcomposition. -/
def dividingCoefficientGradedHecke
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n i : ℤ)
    (K L : CompactOpenLevel (dividingCoefficientDomain σ ℓ Kℓ p hp))
    (g : dividingCoefficientDomain σ ℓ Kℓ p hp) :
    (dividingCoefficientGradedPresheaf σ ℓ Kℓ 𝓛 p hp X n i).obj (op L) ⟶
      (dividingCoefficientGradedPresheaf σ ℓ Kℓ 𝓛 p hp X n i).obj (op K) :=
  coefficientGradedHecke R (σ.finiteAdelicPointsSplit p hp) σ.finiteAdelicDiagonal
    (localCoefficientRep σ ℓ Kℓ 𝓛) X n i K L g

/-- The map of `dividingCoefficientGradedPresheaf X n i` along an arrow `a : K ⟶ L` of levels is
the double-coset operator `[K a L]` of its element. -/
lemma dividingCoefficientGradedPresheaf_map_eq
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n i : ℤ)
    {K L : CompactOpenLevel (dividingCoefficientDomain σ ℓ Kℓ p hp)} (a : K ⟶ L) :
    (dividingCoefficientGradedPresheaf σ ℓ Kℓ 𝓛 p hp X n i).map a.op =
      dividingCoefficientGradedHecke σ ℓ Kℓ 𝓛 p hp X n i K L a.element :=
  coefficientGradedPresheaf_map_eq R _ _ _ X n i a

/-- The Hecke algebra of a compact open level `K` of `dividingCoefficientDomain σ ℓ Kℓ p hp`
acting on the graded piece `gr^i` of the abutment filtration on `Hom(X, A(K)[n])`. -/
def dividingCoefficientGradedHeckeAlgebraHom
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n i : ℤ)
    (K : CompactOpenLevel (dividingCoefficientDomain σ ℓ Kℓ p hp)) :
    LevelHeckeAlgebra R K.subgroup →+*
      End ((dividingCoefficientGradedPresheaf σ ℓ Kℓ 𝓛 p hp X n i).obj (op K)) :=
  coefficientGradedHeckeAlgebraHom R (σ.finiteAdelicPointsSplit p hp) σ.finiteAdelicDiagonal
    (localCoefficientRep σ ℓ Kℓ 𝓛) X n i K

end Langlands.Shimura.DefiniteForms
