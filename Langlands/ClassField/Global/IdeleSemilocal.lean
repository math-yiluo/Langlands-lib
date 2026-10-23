import Langlands.ClassField.Global.IdeleCohomology
import Langlands.Cohomology.ShapiroExplicit

/-! # Semilocal coinduction for the idele group

Shapiro's lemma along an injective group homomorphism, the morphism into a coinduced
representation adjoint to a coefficient map, and the coset sum out of it; applied to the
idele group `J_E` and the decomposition map `decompositionHom v w`.
-/

noncomputable section

universe u

open CategoryTheory

namespace Langlands.Shapiro

set_option backward.isDefEq.respectTransparency false

section Injective

variable {k G H : Type u} [CommRing k] [Group G] [Group H] (φ : H →* G)

/-- Evaluation at the identity, `Res_φ (Coind_φ A) ⟶ A`, `f ↦ f 1`. -/
def coindEvalOf (A : Rep.{u} k H) : Rep.res φ (Rep.coind φ A) ⟶ A :=
  Rep.ofHom ⟨(LinearMap.proj (1 : G)).comp (A.ρ.coindV φ).subtype, fun h => by
    ext f
    change f.1 (1 * φ h) = A.ρ h (f.1 1)
    rw [one_mul, ← f.2 h 1, mul_one]⟩

@[simp]
lemma coindEvalOf_hom_apply (A : Rep.{u} k H) (f : Rep.coind φ A) :
    (coindEvalOf φ A).hom f = f.1 1 := rfl

/-- The explicit Shapiro map `Hⁿ(G, Coind_φ A) ⟶ Hⁿ(H, A)` along `φ : H →* G`: restriction
of cochains along `φ` followed by evaluation of the coefficients at the identity. -/
abbrev shapiroMapOf (A : Rep.{u} k H) (n : ℕ) :
    groupCohomology (Rep.coind φ A) n ⟶ groupCohomology A n :=
  groupCohomology.map φ (coindEvalOf φ A) n

variable {φ}

/-- The identity on functions, from `Coind_φ A` to `Coind` along the inclusion of the range. -/
def coindToRange (hφ : Function.Injective φ) (A : Rep.{u} k H) :
    Rep.coind φ A ⟶
      Rep.coind φ.range.subtype (Rep.res (MonoidHom.ofInjective hφ).symm.toMonoidHom A) :=
  Rep.ofHom
    { toFun f := ⟨f.1, fun s g => by
        have h := f.2 ((MonoidHom.ofInjective hφ).symm s) g
        have hs : φ ((MonoidHom.ofInjective hφ).symm s) = s :=
          congrArg Subtype.val ((MonoidHom.ofInjective hφ).apply_symm_apply s)
        rw [hs] at h
        exact h⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl
      isIntertwining' _ := rfl }

/-- The identity on functions, from `Coind` along the inclusion of the range to `Coind_φ A`. -/
def coindOfRange (hφ : Function.Injective φ) (A : Rep.{u} k H) :
    Rep.coind φ.range.subtype (Rep.res (MonoidHom.ofInjective hφ).symm.toMonoidHom A) ⟶
      Rep.coind φ A :=
  Rep.ofHom
    { toFun f := ⟨f.1, fun h g => by
        have hf := f.2 (MonoidHom.ofInjective hφ h) g
        change f.1 (φ h * g) =
          A.ρ ((MonoidHom.ofInjective hφ).symm (MonoidHom.ofInjective hφ h)) (f.1 g) at hf
        rwa [MulEquiv.symm_apply_apply] at hf⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl
      isIntertwining' _ := rfl }

/-- The identity of `A`, from `A` restricted along `H ≃* φ.range` and back. -/
def resRangeHom (hφ : Function.Injective φ) (A : Rep.{u} k H) :
    Rep.res (MonoidHom.ofInjective hφ).toMonoidHom
        (Rep.res (MonoidHom.ofInjective hφ).symm.toMonoidHom A) ⟶ A :=
  Rep.ofHom
    { toLinearMap := LinearMap.id
      isIntertwining' h := by
        ext a
        change A.ρ ((MonoidHom.ofInjective hφ).symm (MonoidHom.ofInjective hφ h)) a = A.ρ h a
        rw [MulEquiv.symm_apply_apply] }

/-- The Shapiro map along `φ` factors through Shapiro along the inclusion of the range. -/
lemma shapiroMapOf_eq (hφ : Function.Injective φ) (A : Rep.{u} k H) (n : ℕ) :
    shapiroMapOf φ A n =
      groupCohomology.map (MonoidHom.id G) (coindToRange hφ A) n ≫
        shapiroMap φ.range _ n ≫
          groupCohomology.map (MonoidHom.ofInjective hφ).toMonoidHom (resRangeHom hφ A) n := by
  rw [shapiroMap, ← groupCohomology.map_comp, ← groupCohomology.map_comp]
  exact groupCohomology.map_congr (by ext; rfl) (by ext; rfl) n

/-- **Shapiro's lemma** along an injective homomorphism `φ : H →* G`. -/
theorem isIso_shapiroMapOf (hφ : Function.Injective φ) (A : Rep.{u} k H) (n : ℕ) :
    IsIso (shapiroMapOf φ A n) := by
  let e : Rep.coind φ A ≅
      Rep.coind φ.range.subtype (Rep.res (MonoidHom.ofInjective hφ).symm.toMonoidHom A) :=
    ⟨coindToRange hφ A, coindOfRange hφ A, by ext; rfl, by ext; rfl⟩
  have h₁ : IsIso (groupCohomology.map (A := Rep.coind φ A) (MonoidHom.id G)
      (coindToRange hφ A) n) :=
    Iso.isIso_hom ((groupCohomology.functor k G n).mapIso e)
  have h₂ := isIso_shapiroMap φ.range
    (Rep.res (MonoidHom.ofInjective hφ).symm.toMonoidHom A) n
  have h₃ : IsIso (groupCohomology.map (MonoidHom.ofInjective hφ).toMonoidHom
      (resRangeHom hφ A) n) := by
    have : groupCohomology.map (MonoidHom.ofInjective hφ).toMonoidHom (resRangeHom hφ A) n =
        (groupCohomology.mapIso (MonoidHom.ofInjective hφ).symm
          (B := Rep.res (MonoidHom.ofInjective hφ).symm.toMonoidHom A) (A := A)
          (LinearEquiv.refl k A.V) (fun _ => rfl) n).hom := by
      rw [groupCohomology.mapIso_hom]
      exact groupCohomology.map_congr (MonoidHom.ext fun _ => rfl) rfl n
    rw [this]
    infer_instance
  rw [shapiroMapOf_eq hφ]
  infer_instance

/-- Shapiro's isomorphism `Hⁿ(G, Coind_φ A) ≅ Hⁿ(H, A)` along an injective `φ`. -/
def shapiroIsoOf (hφ : Function.Injective φ) (A : Rep.{u} k H) (n : ℕ) :
    groupCohomology (Rep.coind φ A) n ≅ groupCohomology A n :=
  @asIso _ _ _ _ (shapiroMapOf φ A n) (isIso_shapiroMapOf hφ A n)

@[simp]
lemma shapiroIsoOf_hom (hφ : Function.Injective φ) (A : Rep.{u} k H) (n : ℕ) :
    (shapiroIsoOf hφ A n).hom = shapiroMapOf φ A n :=
  rfl

variable (φ)

/-- The adjoint morphism `B ⟶ Coind_φ A` of a coefficient map `π`, followed by evaluation at
the identity, is `π`. -/
@[reassoc (attr := simp)]
lemma res_resCoindToHom_comp_coindEvalOf {B : Rep.{u} k G} {A : Rep.{u} k H}
    (π : Rep.res φ B ⟶ A) :
    (Rep.resFunctor φ).map (Rep.resCoindToHom φ B A π) ≫ coindEvalOf φ A = π := by
  ext b
  change π.hom (B.ρ 1 b) = π.hom b
  rw [map_one]
  rfl

/-- The map `Hⁿ(G, B) ⟶ Hⁿ(H, A)` induced by `π : Res_φ B ⟶ A` factors through
`Hⁿ(G, Coind_φ A)` and the Shapiro map. -/
lemma map_resCoindToHom_comp_shapiroMapOf {B : Rep.{u} k G} {A : Rep.{u} k H}
    (π : Rep.res φ B ⟶ A) (n : ℕ) :
    groupCohomology.map (MonoidHom.id G) (Rep.resCoindToHom φ B A π) n ≫ shapiroMapOf φ A n =
      groupCohomology.map φ π n := by
  rw [shapiroMapOf, ← groupCohomology.map_comp]
  exact groupCohomology.map_congr (by ext; rfl)
    (by ext b; change π.hom (B.ρ 1 b) = π.hom b; rw [map_one]; rfl) n

end Injective

section CosetSum

variable {k G H : Type u} [CommRing k] [Group G] [Group H] (φ : H →* G)
  {A : Rep.{u} k H} {B : Rep.{u} k G}

/-- The term of the coset sum at the left coset `x φ(H)`: `f ↦ x • ι (f x⁻¹)`; it does not
depend on the representative `x`. -/
def cosetTerm (ι : A ⟶ Rep.res φ B) (c : G ⧸ φ.range) : (Rep.coind φ A).V →ₗ[k] B.V :=
  Quotient.liftOn' c
    (fun x => B.ρ x ∘ₗ ι.hom.toLinearMap ∘ₗ (LinearMap.proj x⁻¹ ∘ₗ (A.ρ.coindV φ).subtype))
    fun x y hxy => by
      obtain ⟨h, hh⟩ := QuotientGroup.leftRel_apply.mp hxy
      obtain rfl : y = x * φ h := by rw [hh, mul_inv_cancel_left]
      ext f
      change B.ρ x (ι.hom (f.1 x⁻¹)) = B.ρ (x * φ h) (ι.hom (f.1 (x * φ h)⁻¹))
      have e₁ : (x * φ h)⁻¹ = φ h⁻¹ * x⁻¹ := by rw [mul_inv_rev, map_inv]
      rw [e₁, f.2 h⁻¹ x⁻¹, Rep.hom_comm_apply ι h⁻¹ (f.1 x⁻¹)]
      change B.ρ x (ι.hom (f.1 x⁻¹)) = B.ρ (x * φ h) (B.ρ (φ h⁻¹) (ι.hom (f.1 x⁻¹)))
      rw [← Module.End.mul_apply, ← map_mul, mul_assoc, ← map_mul, mul_inv_cancel, map_one,
        mul_one]

@[simp]
lemma cosetTerm_mk (ι : A ⟶ Rep.res φ B) (x : G) (f : Rep.coind φ A) :
    cosetTerm φ ι (x : G ⧸ φ.range) f = B.ρ x (ι.hom (f.1 x⁻¹)) :=
  rfl

variable [Fintype (G ⧸ φ.range)]

/-- The coset sum `Coind_φ A ⟶ B` of an `H`-morphism `ι : A ⟶ Res_φ B`:
`f ↦ ∑_{x φ(H) ∈ G ⧸ φ(H)} x • ι (f x⁻¹)`. -/
def coindSum (ι : A ⟶ Rep.res φ B) : Rep.coind φ A ⟶ B :=
  Rep.ofHom
    { toLinearMap := ∑ c, cosetTerm φ ι c
      isIntertwining' g := by
        ext f
        change (∑ c, cosetTerm φ ι c) ((Rep.coind φ A).ρ g f) =
          B.ρ g ((∑ c, cosetTerm φ ι c) f)
        rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
        refine (Fintype.sum_equiv (MulAction.toPerm g) _ _ fun c => ?_).symm
        induction c using QuotientGroup.induction_on with | H x => ?_
        change B.ρ g (B.ρ x (ι.hom (f.1 x⁻¹))) = B.ρ (g * x) (ι.hom (f.1 ((g * x)⁻¹ * g)))
        rw [mul_inv_rev, inv_mul_cancel_right, map_mul, Module.End.mul_apply] }

lemma coindSum_hom_apply (ι : A ⟶ Rep.res φ B) (f : Rep.coind φ A) :
    (coindSum φ ι).hom f = ∑ c, cosetTerm φ ι c f :=
  LinearMap.sum_apply _ _ _

/-- If `π ∘ ι = id` and `π (g • ι a) = 0` for `g ∉ φ(H)`, then the coset sum of `ι` is a
section of the morphism `B ⟶ Coind_φ A` adjoint to `π`. -/
theorem coindSum_comp_resCoindToHom (ι : A ⟶ Rep.res φ B) (π : Rep.res φ B ⟶ A)
    (hιπ : ∀ a, π.hom (ι.hom a) = a)
    (hπ : ∀ g ∉ φ.range, ∀ a, π.hom (B.ρ g (ι.hom a)) = 0) :
    coindSum φ ι ≫ Rep.resCoindToHom φ B A π = 𝟙 _ := by
  ext f g
  change π.hom (B.ρ g ((coindSum φ ι).hom f)) = f.1 g
  rw [coindSum_hom_apply, map_sum, map_sum, Finset.sum_eq_single ((g⁻¹ : G) : G ⧸ φ.range)]
  · change π.hom (B.ρ g (B.ρ g⁻¹ (ι.hom (f.1 g⁻¹⁻¹)))) = f.1 g
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, inv_inv]
    exact hιπ _
  · intro c _ hc
    induction c using QuotientGroup.induction_on with | H x => ?_
    change π.hom (B.ρ g (B.ρ x (ι.hom (f.1 x⁻¹)))) = 0
    rw [← Module.End.mul_apply, ← map_mul]
    refine hπ _ (fun hx => hc ?_) _
    rw [QuotientGroup.eq, ← mul_inv_rev]
    exact Subgroup.inv_mem _ hx
  · intro h
    exact absurd (Finset.mem_univ _) h

end CosetSum

end Langlands.Shapiro

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.ClassFieldTheory.Local
open CategoryTheory FundamentalClass

section Transport

/-- If `finitePlaceEquiv e p = q`, then `e` extends to a continuous ring isomorphism between
the completions at `q` and at `p`. -/
theorem exists_completionEquiv_of_finitePlaceEquiv_eq {K L : Type u} [Field K]
    [NumberField K] [Field L] [NumberField L] (e : K ≃+* L) (p : HeightOneSpectrum (𝓞 L))
    (q : HeightOneSpectrum (𝓞 K)) (h : finitePlaceEquiv e p = q) :
    ∃ τ : q.adicCompletion K ≃+* p.adicCompletion L, Continuous τ ∧
      ∀ a : K, τ (algebraMap K _ a) = algebraMap L _ (e a) := by
  subst h
  exact ⟨finiteCompletionEquiv e p, continuous_finiteCompletionEquiv e p,
    finiteCompletionEquiv_coe e p⟩

/-- The `w'`-coordinate of `g` applied to an idele concentrated at `w` is trivial when `g`
does not move `w'` to `w`. -/
theorem ideleCoordinate_relativeIdeleAut_ofAdicCompletion_of_ne {F E : Type u} [Field F]
    [Field E] [NumberField E] [Algebra F E] (w w' : HeightOneSpectrum (𝓞 E)) (g : E ≃ₐ[F] E)
    (hg : finitePlaceEquiv g.toRingEquiv w' ≠ w) (y : (w.adicCompletion E)ˣ) :
    ideleCoordinate w' (relativeIdeleAut F E g (IdeleGroup.ofAdicCompletion (𝓞 E) E w y)) =
      1 := by
  classical
  apply Units.ext
  change finiteCompletionEquiv g.toRingEquiv w'
      (Pi.mulSingle w (y : w.adicCompletion E) (finitePlaceEquiv g.toRingEquiv w')) = 1
  rw [Pi.mulSingle_eq_of_ne hg, map_one]

end Transport

section Semilocal

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Normal F E] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
  [w.asIdeal.LiesOver v.asIdeal]

/-- The decomposition map `Gal(E_w/F_v) → Gal(E/F)` is injective. -/
theorem decompositionHom_injective : Function.Injective (decompositionHom v w) := by
  intro σ τ h
  apply AlgEquiv.ext
  intro x
  have := (denseRange_algebraMap E w).equalizer (continuous_localAut v w σ)
    (continuous_localAut v w τ) (funext fun a => by
      change σ (algebraMap E _ a) = τ (algebraMap E _ a)
      rw [← algebraMap_decompositionHom, ← algebraMap_decompositionHom, h])
  exact congrFun this x

/-- The image of `decompositionHom v w` is the stabilizer of `w`. -/
theorem mem_range_decompositionHom_iff (g : E ≃ₐ[F] E) :
    g ∈ (decompositionHom v w).range ↔ finitePlaceEquiv g.toRingEquiv w = w := by
  constructor
  · rintro ⟨σ, rfl⟩
    exact finitePlaceEquiv_decompositionHom v w σ
  · intro hg
    obtain ⟨τ, hτ, hτg⟩ :=
      exists_completionEquiv_of_finitePlaceEquiv_eq g.toRingEquiv w w hg
    have hlin : ∀ c : v.adicCompletion F,
        τ (algebraMap (v.adicCompletion F) (w.adicCompletion E) c) =
          algebraMap (v.adicCompletion F) (w.adicCompletion E) c := by
      intro c
      have := (denseRange_algebraMap F v).equalizer
        (hτ.comp (FiniteExtension.continuous_completionMap v w))
        (FiniteExtension.continuous_completionMap v w) (funext fun a => by
          change τ (FiniteExtension.completionMap v w (algebraMap F _ a)) =
            FiniteExtension.completionMap v w (algebraMap F _ a)
          rw [FiniteExtension.completionMap_coe, hτg]
          change algebraMap E _ (g (algebraMap F E a)) = _
          rw [g.commutes])
      exact congrFun this c
    refine ⟨AlgEquiv.ofRingEquiv (f := τ) hlin, ?_⟩
    apply AlgEquiv.ext
    intro x
    apply (algebraMap E (w.adicCompletion E)).injective
    rw [algebraMap_decompositionHom]
    exact hτg x

/-- The semilocal projection `J_E ⟶ Coind(E_wˣ)` along `decompositionHom v w`,
`x ↦ (g ↦ (g • x)_w)`: the morphism adjoint to the local projection. -/
def ideleSemilocalProjection :
    relativeIdeleRepresentation F E ⟶
      Rep.coind (decompositionHom v w)
        (unitsRepresentation (padicField v).Carrier (w.adicCompletion E)) :=
  Rep.resCoindToHom (decompositionHom v w) _ _ (ideleLocalProjection v w)

/-- The local map factors through the semilocal projection and the Shapiro map. -/
theorem ideleLocalMap_eq (n : ℕ) :
    ideleLocalMap v w n =
      groupCohomology.map (MonoidHom.id _) (ideleSemilocalProjection v w) n ≫
        Shapiro.shapiroMapOf (decompositionHom v w) _ n :=
  (Shapiro.map_resCoindToHom_comp_shapiroMapOf _ _ n).symm

variable [Fintype ((E ≃ₐ[F] E) ⧸ (decompositionHom v w).range)]

/-- The semilocal section `Coind(E_wˣ) ⟶ J_E` along `decompositionHom v w`: the coset sum
`f ↦ ∑_{g D_w} g • ι_w (f g⁻¹)` of the single-coordinate embedding `ι_w`. -/
def ideleSemilocalSection :
    Rep.coind (decompositionHom v w)
        (unitsRepresentation (padicField v).Carrier (w.adicCompletion E)) ⟶
      relativeIdeleRepresentation F E :=
  Shapiro.coindSum (decompositionHom v w) (ideleLocalEmbedding v w)

/-- The semilocal section is a section of the semilocal projection. -/
@[reassoc (attr := simp)]
theorem ideleSemilocalSection_comp_ideleSemilocalProjection :
    ideleSemilocalSection v w ≫ ideleSemilocalProjection v w = 𝟙 _ :=
  Shapiro.coindSum_comp_resCoindToHom _ _ _
    (fun a => congrArg Additive.ofMul (ideleCoordinate_ofAdicCompletion_self w
      (@Additive.toMul (w.adicCompletion E)ˣ a)))
    (fun g hg a => congrArg Additive.ofMul
      (ideleCoordinate_relativeIdeleAut_ofAdicCompletion_of_ne w w g
        (fun h => hg ((mem_range_decompositionHom_iff v w g).2 h))
        (@Additive.toMul (w.adicCompletion E)ˣ a)))

/-- A section of the local map `Hⁿ(Gal(E/F), J_E) → Hⁿ(Gal(E_w/F_v), E_wˣ)`: the inverse
Shapiro isomorphism followed by the map induced by the semilocal section. -/
def ideleLocalSection (n : ℕ) :
    relativeCohomology (padicField v).Carrier (w.adicCompletion E) n ⟶
      relativeIdeleCohomology F E n :=
  (Shapiro.shapiroIsoOf (decompositionHom_injective v w) _ n).inv ≫
    groupCohomology.map (MonoidHom.id _) (ideleSemilocalSection v w) n

/-- The local map `Hⁿ(Gal(E/F), J_E) → Hⁿ(Gal(E_w/F_v), E_wˣ)` is a split epimorphism. -/
@[reassoc (attr := simp)]
theorem ideleLocalSection_comp_ideleLocalMap (n : ℕ) :
    ideleLocalSection v w n ≫ ideleLocalMap v w n = 𝟙 _ := by
  rw [ideleLocalMap_eq, ideleLocalSection, Category.assoc,
    ← groupCohomology.map_id_comp_assoc, ideleSemilocalSection_comp_ideleSemilocalProjection,
    groupCohomology.map_id, Category.id_comp,
    ← Shapiro.shapiroIsoOf_hom (decompositionHom_injective v w), Iso.inv_hom_id]

end Semilocal

section Orthogonality

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Normal F E] (v v' : HeightOneSpectrum (𝓞 F)) (w w' : HeightOneSpectrum (𝓞 E))
  [w.asIdeal.LiesOver v.asIdeal] [w'.asIdeal.LiesOver v'.asIdeal]
  [Fintype ((E ≃ₐ[F] E) ⧸ (decompositionHom v w).range)]

/-- The semilocal section at `w`, followed by the local projection at `w'`, is zero when no
element of `Gal(E/F)` moves `w'` to `w`. -/
theorem ideleSemilocalSection_comp_ideleLocalProjection_of_ne
    (h : ∀ g : E ≃ₐ[F] E, finitePlaceEquiv g.toRingEquiv w' ≠ w) :
    (Rep.resFunctor (decompositionHom v' w')).map (ideleSemilocalSection v w) ≫
      ideleLocalProjection v' w' = 0 := by
  ext f
  change ideleCoordinateLinear v' w' ((ideleSemilocalSection v w).hom f) = 0
  rw [ideleSemilocalSection, Shapiro.coindSum_hom_apply, map_sum]
  refine Finset.sum_eq_zero fun c _ => ?_
  induction c using QuotientGroup.induction_on with | H x => ?_
  exact congrArg Additive.ofMul
    (ideleCoordinate_relativeIdeleAut_ofAdicCompletion_of_ne w w' x (h x) _)

/-- The section of the local map at `w`, followed by the local map at `w'`, is zero when no
element of `Gal(E/F)` moves `w'` to `w`. -/
theorem ideleLocalSection_comp_ideleLocalMap_of_ne
    (h : ∀ g : E ≃ₐ[F] E, finitePlaceEquiv g.toRingEquiv w' ≠ w) (n : ℕ) :
    ideleLocalSection v w n ≫ ideleLocalMap v' w' n = 0 := by
  rw [ideleLocalSection, Category.assoc, ideleLocalMap, ← groupCohomology.map_comp,
    ideleSemilocalSection_comp_ideleLocalProjection_of_ne v v' w w' h, groupCohomology.map,
    groupCohomology.cochainsMap_zero, HomologicalComplex.homologyMap_zero]
  exact Limits.comp_zero

end Orthogonality

end Langlands.ClassField.Global
