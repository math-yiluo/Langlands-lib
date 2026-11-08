import Langlands.Shimura.DefiniteFormsSmoothExt
import Langlands.Shimura.EquivariantFormsHecke
import Langlands.Shimura.DefiniteFormsDoubleCoset
import Langlands.Cohomology.HyperextAbutmentFunctor

/-!
# Forms with coefficients as smooth representations of one factor, and their Ext

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, 1999, p.311,
Proposition 4.10, gives a spectral sequence of `𝒪`-modules
`E₂^{i,j} = Ext^i(H_c^{2(n-1)-j}(M̌_N, L_ℓ(n-1)), 𝒜_ℓ(GJ, ρ, H)) ⇒ H^{i+j}(S̄_{K(N)}, W~)`,
where "`Ext^i` denotes the `i`-th derived functor of `Hom` in the category of smooth
`L_ℓ[GJ]`-modules", and "as `K(N)^{ℓ,p}`-varies the spectral sequences are
`GG(𝔸_f^{ℓ,p})`-equivariant". Unlike Proposition 4.4, the coefficients are a representation
`ρ` of `K_ℓ`, so the level away from `p` acts nontrivially on them. This file constructs the
smooth `GJ_p`-modules of forms with such coefficients, their `Ext` groups, the hyperext spectral
sequence with its second page and abutment, and their variation with the level away from `p`.
It does not construct `M̌_N`, its cohomology, the Shimura variety or the `ℓ`-adic limit, and does
not prove convergence or the comparison with `H^{i+j}(S̄_{K(N)}, W~)`.

## Main definitions

For groups `Γ`, `G` with `ι : Γ →* G`, an isomorphism of topological groups
`e : G ≃ₜ* H × H'`, a subgroup `D` of `G` and a representation `ρ` of `D`, in the namespace
`EquivariantForms`:

* `coefficientDomain e D`: the elements `k` of `H'` with `e⁻¹ (1, k) ∈ D`; `domainLevel e K'`
  is a subgroup `K'` of it viewed in `H'`.
* `coefficientForms R e ι ρ K'`: the functions `f : G → V` with `f (ι γ * g) = f g` and
  `f (g * k) = ρ k⁻¹ (f g)` for `k ∈ e⁻¹ (1 × K')`, with right translation
  `coefficientTranslation` by `H` and `coefficientTransport` along elements `c` of the
  coefficient domain between levels, `f ↦ (x ↦ ρ (e⁻¹ (1, c)) (f (x * e⁻¹ (1, c))))`.
* `coefficientFixedEquiv`: the vectors fixed by `U ≤ H` are the forms of level `e⁻¹ (U × K')`
  with coefficients `ρ` composed with `splitCoefficientHom`, `k ↦ e⁻¹ (1, (e k).2)`;
  `coefficientSmoothFixedEquiv` for the smooth part.
* `coefficientFormsPresheaf`, `coefficientSmoothPresheaf`: the presheaves
  `K' ↦ coefficientForms` of representations and of smooth representations of `H` on compact
  open levels `K'` of the coefficient domain.
* `coefficientExtPresheaf W i`, `coefficientSpectralSequence X K'`,
  `coefficientSecondPageAddEquiv`, `coefficientAbutmentPresheaf`, `coefficientAbutmentIso`,
  `coefficientFiltrationPresheaf`, `coefficientGradedPresheaf`: `Ext^i(W, -)` of these forms,
  the published hyperext spectral sequence with its second page, and the intended abutment
  `Hom(X, A(K')[n])` with its filtration steps and graded pieces as presheaves in `K'`;
  `coefficientFiltrationι`, `coefficientFiltrationMapOfLE` and `coefficientGradedπ` are the
  natural maps between them.

In the namespace `DefiniteForms`, for `σ : AlgebraInvolution ℚ A`, a finite place `ℓ`, a
subgroup `Kℓ` of the `ℓ`-adic points, a representation `𝓛` of `Kℓ`, `p ≠ 0` and the published
splitting `σ.finiteAdelicPointsSplit p hp : GJ(𝔸_f) ≃ₜ* GJ(∏_{v ∣ p} ℚ_v) × GJ(𝔸_f^{(p)})`:

* `localCoefficientDomain σ ℓ Kℓ`, `localCoefficientMap`, `localCoefficientRep`: the finite
  adelic points with `ℓ`-component in `Kℓ`, the `ℓ`-component map to `Kℓ`, and `𝓛` composed
  with it.
* `dividingCoefficientDomain σ ℓ Kℓ p hp`: the corresponding coefficient domain in
  `GJ(𝔸_f^{(p)})`; `coefficientForms_eq_ellModuleForms` identifies the forms of level
  `e⁻¹ (1 × K')` with the published Harris `𝒜_ℓ(GJ, 𝓛, K)` (3.7) at `K = e⁻¹ (1 × K')`.
* `dividingCoefficientSmoothPresheaf`, `dividingCoefficientSmoothFixedEquiv`,
  `dividingCoefficientExtPresheaf`, `dividingCoefficientSpectralSequence`,
  `dividingCoefficientSecondPageAddEquiv`, `dividingCoefficientAbutmentPresheaf`,
  `dividingCoefficientAbutmentIso`, `dividingCoefficientFiltrationPresheaf`,
  `dividingCoefficientGradedPresheaf`, `dividingCoefficientFiltrationι`,
  `dividingCoefficientFiltrationMapOfLE` and `dividingCoefficientGradedπ`.

No hypothesis `ℓ ∤ p` is needed for the definitions. For a place `ℓ` whose prime ideal contains
`p`, the `ℓ`-component of `e⁻¹ (1, k)` is trivial (`finiteLocalMap_awayHom`), the coefficient
domain is everything (`dividingCoefficientDomain_eq_top`) and the forms are those with trivial
coefficients (`coefficientForms_eq_awayLevelForms`).
-/

noncomputable section

namespace Langlands.Shimura.EquivariantForms

open CategoryTheory CategoryTheory.Limits Opposite DerivedCategory
open Langlands.Cohomology Langlands.Shimura.CompactOpenLevel

universe t uR uΓ uG uH uH' u w

section Coefficients

variable (R : Type uR) [CommRing R] {Γ : Type uΓ} {G : Type uG} {H : Type uH} {H' : Type uH'}
  [Group Γ] [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] [Group H']
  [TopologicalSpace H'] (e : G ≃ₜ* H × H') (ι : Γ →* G) {D : Subgroup G} {V : Type t}
  [AddCommGroup V] [Module R V] (ρ : Representation R D V)

/-- The endomorphism `g ↦ e⁻¹ (1, (e g).2)` of `G`: the component of `g` in the second
factor. -/
def awayPart : G →* G :=
  (awayHom e).comp ((MonoidHom.snd H H').comp (e : G →* H × H'))

lemma awayPart_apply (g : G) : awayPart e g = awayHom e (e g).2 :=
  rfl

lemma awayPart_factorHom (h : H) : awayPart e (factorHom e h) = 1 := by
  rw [awayPart_apply, factorHom_apply, e.apply_symm_apply, map_one]

lemma awayPart_eq_self_of_mem {K' : Subgroup H'} {g : G} (hg : g ∈ awayLevel e K') :
    awayPart e g = g := by
  obtain ⟨a, -, rfl⟩ := (mem_awayLevel (e := e)).1 hg
  rw [awayPart_apply, awayHom_apply, awayHom_apply, e.apply_symm_apply]

variable (D) in
/-- The subgroup of the second factor `H'` of the elements `k` with `e⁻¹ (1, k) ∈ D`. -/
def coefficientDomain : Subgroup H' :=
  D.comap (awayHom e)

variable {e} in
lemma awayHom_mem_of_mem_coefficientDomain {k : H'} (hk : k ∈ coefficientDomain e D) :
    awayHom e k ∈ D :=
  hk

/-- The subgroup `K'.map C.subtype` of `H'`, for a subgroup `K'` of the coefficient domain
`C`. -/
abbrev domainLevel (K' : Subgroup (coefficientDomain e D)) : Subgroup H' :=
  K'.map (coefficientDomain e D).subtype

lemma awayLevel_domainLevel_le (K' : Subgroup (coefficientDomain e D)) :
    awayLevel e (domainLevel e K') ≤ D :=
  Subgroup.map_le_iff_le_comap.2 (Subgroup.map_subtype_le K')

/-- Forms of level `e⁻¹ (1 × K')` with coefficients `ρ`, for a subgroup `K'` of the coefficient
domain: the functions `f : G → V` with `f (ι γ * g) = f g` and `f (g * k) = ρ k⁻¹ (f g)` for
`k ∈ e⁻¹ (1 × K')`. -/
abbrev coefficientForms (K' : Subgroup (coefficientDomain e D)) : Submodule R (G → V) :=
  forms ι (awayLevel e (domainLevel e K'))
    (ρ.comp (Subgroup.inclusion (awayLevel_domainLevel_le e K')))

/-- Right translation `(h • f) g = f (g * e⁻¹ (h, 1))` by the first factor `H` on the forms of
level `e⁻¹ (1 × K')` with coefficients `ρ`: the published `rightTranslation` along
`factorHom e`. -/
def coefficientTranslation (K' : Subgroup (coefficientDomain e D)) :
    Representation R H (coefficientForms R e ι ρ K') :=
  rightTranslation ι _ _ (factorHom e) (factorHom_mul_awayLevel e (domainLevel e K'))

@[simp]
lemma coefficientTranslation_apply_coe (K' : Subgroup (coefficientDomain e D)) (h : H)
    (f : coefficientForms R e ι ρ K') (g : G) :
    (coefficientTranslation R e ι ρ K' h f).1 g = f.1 (g * factorHom e h) :=
  rfl

lemma awayHom_conj_mem {K₁ K₂ : Subgroup (coefficientDomain e D)} (c : coefficientDomain e D)
    (hc : ∀ k ∈ K₁, c⁻¹ * k * c ∈ K₂) :
    ∀ k ∈ awayLevel e (domainLevel e K₁),
      (awayHom e c)⁻¹ * k * awayHom e c ∈ awayLevel e (domainLevel e K₂) := by
  intro k hk
  obtain ⟨a, ha, rfl⟩ := (mem_awayLevel (e := e)).1 hk
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 ha
  rw [← map_inv, ← map_mul, ← map_mul]
  exact awayHom_mem_awayLevel e (Subgroup.mem_map_of_mem _ (hc b hb))

/-- Transport `f ↦ (x ↦ ρ (e⁻¹ (1, c)) (f (x * e⁻¹ (1, c))))` from forms of level
`e⁻¹ (1 × K₂)` to forms of level `e⁻¹ (1 × K₁)`, for `c` in the coefficient domain with
`c⁻¹ K₁ c ⊆ K₂`: the published `transport` along `e⁻¹ (1, c)` with intertwiner
`ρ (e⁻¹ (1, c))`. -/
def coefficientTransport {K₁ K₂ : Subgroup (coefficientDomain e D)} (c : coefficientDomain e D)
    (hc : ∀ k ∈ K₁, c⁻¹ * k * c ∈ K₂) :
    coefficientForms R e ι ρ K₂ →ₗ[R] coefficientForms R e ι ρ K₁ :=
  transport ι _ _ (awayHom e c) (awayHom_conj_mem e c hc)
    (ρ ⟨awayHom e c, awayHom_mem_of_mem_coefficientDomain c.2⟩) fun k w => by
      change ρ _ (ρ _ w) = ρ _ (ρ _ w)
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      ext
      simp [mul_assoc]

@[simp]
lemma coefficientTransport_apply_coe {K₁ K₂ : Subgroup (coefficientDomain e D)}
    (c : coefficientDomain e D) (hc : ∀ k ∈ K₁, c⁻¹ * k * c ∈ K₂)
    (f : coefficientForms R e ι ρ K₂) (x : G) :
    (coefficientTransport R e ι ρ c hc f).1 x =
      ρ ⟨awayHom e c, awayHom_mem_of_mem_coefficientDomain c.2⟩ (f.1 (x * awayHom e c)) :=
  rfl

/-- Transport along the second factor commutes with right translation by the first. -/
def coefficientTransportIntertwining {K₁ K₂ : Subgroup (coefficientDomain e D)}
    (c : coefficientDomain e D) (hc : ∀ k ∈ K₁, c⁻¹ * k * c ∈ K₂) :
    (coefficientTranslation R e ι ρ K₂).IntertwiningMap (coefficientTranslation R e ι ρ K₁) where
  toLinearMap := coefficientTransport R e ι ρ c hc
  isIntertwining' h := by
    ext f x
    change ρ _ (f.1 (x * awayHom e c * factorHom e h)) = ρ _ (f.1 (x * factorHom e h * awayHom e c))
    rw [mul_assoc, mul_assoc, (factorHom_commute_awayHom e h c).eq]

lemma awayPart_mem_of_mem_splitLevel (U : Subgroup H) (K' : Subgroup (coefficientDomain e D))
    {k : G} (hk : k ∈ splitLevel e U (domainLevel e K')) : awayPart e k ∈ D := by
  obtain ⟨c, -, hc⟩ := Subgroup.mem_map.1 (mem_splitLevel.1 hk).2
  rw [awayPart_apply, ← hc]
  exact c.2

/-- The homomorphism `k ↦ e⁻¹ (1, (e k).2)` from `e⁻¹ (U × K')` to `D`, for a subgroup `K'` of
the coefficient domain. -/
def splitCoefficientHom (U : Subgroup H) (K' : Subgroup (coefficientDomain e D)) :
    splitLevel e U (domainLevel e K') →* D :=
  ((awayPart e).comp (splitLevel e U (domainLevel e K')).subtype).codRestrict D
    fun k => awayPart_mem_of_mem_splitLevel e U K' k.2

@[simp]
lemma splitCoefficientHom_apply_coe (U : Subgroup H) (K' : Subgroup (coefficientDomain e D))
    (k : splitLevel e U (domainLevel e K')) :
    (splitCoefficientHom e U K' k : G) = awayPart e k :=
  rfl

/-- The vectors of `coefficientTranslation` fixed by a subgroup `U` of `H` are the forms of level
`e⁻¹ (U × K')` with coefficients `ρ (e⁻¹ (1, (e k).2))`: every `k ∈ e⁻¹ (U × K')` is
`e⁻¹ ((e k).1, 1) * e⁻¹ (1, (e k).2)`, the first factor acts trivially on fixed vectors and the
second through `ρ`. -/
def coefficientFixedEquiv (K' : Subgroup (coefficientDomain e D)) (U : Subgroup H) :
    fixedVectors (coefficientTranslation R e ι ρ K') U ≃ₗ[R]
      forms ι (splitLevel e U (domainLevel e K')) (ρ.comp (splitCoefficientHom e U K')) where
  toFun f := ⟨f.1.1, f.1.2.1, fun g k => by
      obtain ⟨hk₁, hk₂⟩ := mem_splitLevel.1 k.2
      have h₁ := f.1.2.2 (g * factorHom e (e k).1)
        ⟨awayHom e (e k).2, awayHom_mem_awayLevel e hk₂⟩
      have h₂ := congrArg (fun f' : coefficientForms R e ι ρ K' => f'.1 g) (f.2 ⟨(e k).1, hk₁⟩)
      change f.1.1 (g * factorHom e (e k).1 * awayHom e (e k).2) =
        ρ ⟨(awayHom e (e k).2)⁻¹, _⟩ (f.1.1 (g * factorHom e (e k).1)) at h₁
      change f.1.1 (g * factorHom e (e k).1) = f.1.1 g at h₂
      change f.1.1 (g * k) = ρ (splitCoefficientHom e U K' k⁻¹) (f.1.1 g)
      rw [← factorHom_mul_awayHom e (k : G), ← mul_assoc, h₁, h₂, map_inv]
      rfl⟩
  invFun f := ⟨⟨f.1, f.2.1, fun g k =>
      (f.2.2 g ⟨k, awayLevel_le_splitLevel e U _ k.2⟩).trans
        (congrArg (fun d => ρ d (f.1 g))
          (Subtype.ext (awayPart_eq_self_of_mem e (inv_mem k.2))))⟩,
    fun u => Subtype.ext (funext fun g =>
      (f.2.2 g ⟨_, factorHom_mem_splitLevel e _ u.2⟩).trans
        (congrArg (fun d => ρ d (f.1 g))
          (Subtype.ext ((congrArg (awayPart e) (map_inv (factorHom e) (u : H)).symm).trans
            (awayPart_factorHom e _))) |>.trans (by rw [map_one]; rfl)))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
lemma coefficientFixedEquiv_apply_coe (K' : Subgroup (coefficientDomain e D)) (U : Subgroup H)
    (f : fixedVectors (coefficientTranslation R e ι ρ K') U) :
    (coefficientFixedEquiv R e ι ρ K' U f).1 = f.1.1 :=
  rfl

/-- A form of level `e⁻¹ (1 × K')` with coefficients `ρ` is a smooth vector for right translation
by `H` if and only if it is a form of level `e⁻¹ (U × K')` for some open subgroup `U` of `H`. -/
lemma isSmoothVector_coefficientTranslation_iff (K' : Subgroup (coefficientDomain e D))
    (f : coefficientForms R e ι ρ K') :
    IsSmoothVector (coefficientTranslation R e ι ρ K') f ↔
      ∃ U : OpenSubgroup H, f.1 ∈ forms ι (splitLevel e U (domainLevel e K'))
        (ρ.comp (splitCoefficientHom e U K')) :=
  exists_congr fun U => ⟨fun hf => (coefficientFixedEquiv R e ι ρ K' U ⟨f, hf⟩).2,
    fun hf => ((coefficientFixedEquiv R e ι ρ K' U).symm ⟨f.1, hf⟩).2⟩

section Smooth

variable [IsTopologicalGroup H]

/-- The vectors of the smooth part of `coefficientTranslation` fixed by an open subgroup `U` of
`H` are the forms of level `e⁻¹ (U × K')` with coefficients `ρ (e⁻¹ (1, (e k).2))`. -/
def coefficientSmoothFixedEquiv (K' : Subgroup (coefficientDomain e D)) (U : OpenSubgroup H) :
    fixedVectors (V := smoothVectors (coefficientTranslation R e ι ρ K'))
      (smoothPart (coefficientTranslation R e ι ρ K')) U.toSubgroup ≃ₗ[R]
      forms ι (splitLevel e U (domainLevel e K')) (ρ.comp (splitCoefficientHom e U K')) :=
  (smoothPartFixedVectorsEquiv _ U).trans (coefficientFixedEquiv R e ι ρ K' U)

@[simp]
lemma coefficientSmoothFixedEquiv_apply_coe (K' : Subgroup (coefficientDomain e D))
    (U : OpenSubgroup H)
    (f : fixedVectors (V := smoothVectors (coefficientTranslation R e ι ρ K'))
      (smoothPart (coefficientTranslation R e ι ρ K')) U.toSubgroup) :
    (coefficientSmoothFixedEquiv R e ι ρ K' U f).1 = f.1.1.1 :=
  rfl

end Smooth

variable [IsTopologicalGroup H']

/-- The forms of level `e⁻¹ (1 × K')` with coefficients `ρ` and right translation by `H`, for
all compact open levels `K'` of the coefficient domain, as a presheaf on the category of these
levels, with `coefficientTransport` on arrows. -/
def coefficientFormsPresheaf :
    (CompactOpenLevel (coefficientDomain e D))ᵒᵖ ⥤ Rep.{max uG t} R H where
  obj K' := Rep.of (coefficientTranslation R e ι ρ K'.unop.subgroup)
  map a := Rep.ofHom (coefficientTransportIntertwining R e ι ρ a.unop.element a.unop.respects)
  map_id K' := by
    ext f x
    change ρ ⟨awayHom e ((1 : coefficientDomain e D) : H'), _⟩
      (f.1 (x * awayHom e ((1 : coefficientDomain e D) : H'))) = f.1 x
    have h₁ : (⟨awayHom e ((1 : coefficientDomain e D) : H'),
        awayHom_mem_of_mem_coefficientDomain (1 : coefficientDomain e D).2⟩ : D) = 1 :=
      Subtype.ext (by simp)
    rw [h₁, map_one, Module.End.one_apply, OneMemClass.coe_one, map_one, mul_one]
  map_comp a b := by
    ext f x
    change ρ ⟨awayHom e ((b.unop.element * a.unop.element : coefficientDomain e D) : H'), _⟩
        (f.1 (x * awayHom e ((b.unop.element * a.unop.element : coefficientDomain e D) : H'))) =
      ρ ⟨awayHom e (b.unop.element : H'), _⟩ (ρ ⟨awayHom e (a.unop.element : H'), _⟩
        (f.1 (x * awayHom e (b.unop.element : H') * awayHom e (a.unop.element : H'))))
    have h₂ : (⟨awayHom e ((b.unop.element * a.unop.element : coefficientDomain e D) : H'),
        awayHom_mem_of_mem_coefficientDomain (b.unop.element * a.unop.element).2⟩ : D) =
        ⟨awayHom e (b.unop.element : H'),
          awayHom_mem_of_mem_coefficientDomain b.unop.element.2⟩ *
        ⟨awayHom e (a.unop.element : H'),
          awayHom_mem_of_mem_coefficientDomain a.unop.element.2⟩ :=
      Subtype.ext (by simp only [Subgroup.coe_mul, map_mul])
    rw [h₂, map_mul, Module.End.mul_apply, Subgroup.coe_mul, map_mul, mul_assoc]

variable [IsTopologicalGroup H]

/-- The smooth part of `coefficientTranslation`, for all compact open levels `K'` of the
coefficient domain: a presheaf of smooth representations of `H`. -/
def coefficientSmoothPresheaf :
    (CompactOpenLevel (coefficientDomain e D))ᵒᵖ ⥤ SmoothRep.{uR, uH, max uG t} R H :=
  coefficientFormsPresheaf R e ι ρ ⋙ SmoothRep.smoothPartFunctor.{uR, uH, max uG t} R H

end Coefficients

section CoefficientExt

variable (R : Type u) [CommRing R] {Γ : Type uΓ} {G : Type u} {H : Type u} {H' : Type uH'}
  [Group Γ] [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Group H'] [TopologicalSpace H'] [IsTopologicalGroup H'] (e : G ≃ₜ* H × H') (ι : Γ →* G)
  {D : Subgroup G} {V : Type u} [AddCommGroup V] [Module R V] (ρ : Representation R D V)

/-- `Ext^i(W, -)` in smooth representations of `H` of the smooth forms of level `e⁻¹ (1 × K')`
with coefficients `ρ`, for all compact open levels `K'` of the coefficient domain, as a presheaf
of `R`-modules. -/
def coefficientExtPresheaf (W : SmoothRep.{u, u, u} R H) (i : ℕ) :
    (CompactOpenLevel (coefficientDomain e D))ᵒᵖ ⥤ ModuleCat.{u} R :=
  coefficientSmoothPresheaf R e ι ρ ⋙ SmoothExt.ext R H W i

variable [HasDerivedCategory.{w} (SmoothRep.{u, u, u} R H)]

/-- The hyperext spectral sequence of an object `X` of the derived category of smooth
representations of `H` and the smooth forms of level `e⁻¹ (1 × K')` with coefficients `ρ`
placed in degree `0`. -/
def coefficientSpectralSequence (X : DerivedCategory (SmoothRep.{u, u, u} R H))
    (K' : CompactOpenLevel (coefficientDomain e D)) :
    E₂CohomologicalSpectralSequence AddCommGrpCat.{w} :=
  HyperextSpectralSequence.hyperextSpectralSequence TStructure.t X
    ((singleFunctor _ 0).obj ((coefficientSmoothPresheaf R e ι ρ).obj (op K')))

/-- The object in position `(p, q)` on page 2 of `coefficientSpectralSequence X K'` is
`Ext^p(H^{-q}(X), -)` of the smooth forms of level `e⁻¹ (1 × K')` with coefficients `ρ`. -/
def coefficientSecondPageAddEquiv (X : DerivedCategory (SmoothRep.{u, u, u} R H))
    (K' : CompactOpenLevel (coefficientDomain e D)) (p : ℕ) (q : ℤ) :
    ((coefficientSpectralSequence R e ι ρ X K').page 2).X ⟨p, q⟩ ≃+
      (coefficientExtPresheaf R e ι ρ ((homologyFunctor _ (-q)).obj X) p).obj (op K') :=
  SmoothHyperext.secondPageAddEquiv R H X _ p q

/-- The intended abutment `Hom(X, A(K')[n])` in total degree `n`, for the smooth forms `A(K')` of
level `e⁻¹ (1 × K')` with coefficients `ρ` placed in degree `0`, as a presheaf of abelian groups
on compact open levels `K'` of the coefficient domain. -/
def coefficientAbutmentPresheaf (X : DerivedCategory (SmoothRep.{u, u, u} R H)) (n : ℤ) :
    (CompactOpenLevel (coefficientDomain e D))ᵒᵖ ⥤ AddCommGrpCat.{w} :=
  coefficientSmoothPresheaf R e ι ρ ⋙ singleFunctor _ 0 ⋙ shiftFunctor _ n ⋙
    preadditiveCoyoneda.obj (op X)

/-- The term of the spectral object of `coefficientSpectralSequence X K'` in degree `n` for the
arrow `⊥ ⟶ ⊤` is the value at `K'` of `coefficientAbutmentPresheaf X n`. -/
def coefficientAbutmentIso (X : DerivedCategory (SmoothRep.{u, u, u} R H))
    (K' : CompactOpenLevel (coefficientDomain e D)) (n : ℤ) :
    ((HyperextSpectralSequence.hyperextSpectralObject TStructure.t X
        ((singleFunctor _ 0).obj ((coefficientSmoothPresheaf R e ι ρ).obj (op K')))).H n).obj
        (ComposableArrows.mk₁ (homOfLE (show (⊥ : EInt) ≤ ⊤ from bot_le))) ≅
      (coefficientAbutmentPresheaf R e ι ρ X n).obj (op K') :=
  HyperextSpectralSequence.abutmentIso _ _ _ n

/-- The step `F^p` of the abutment filtration on `Hom(X, A(K')[n])`, for all compact open levels
`K'` of the coefficient domain, as a presheaf of abelian groups by postcomposition. -/
def coefficientFiltrationPresheaf (X : DerivedCategory (SmoothRep.{u, u, u} R H)) (n p : ℤ) :
    (CompactOpenLevel (coefficientDomain e D))ᵒᵖ ⥤ AddCommGrpCat.{w} :=
  coefficientSmoothPresheaf R e ι ρ ⋙ singleFunctor _ 0 ⋙
    HyperextAbutment.filtrationFunctor TStructure.t X n p

/-- The graded piece `gr^p = F^p / F^{p+1}` of the abutment filtration on `Hom(X, A(K')[n])`,
for all compact open levels `K'` of the coefficient domain, as a presheaf of abelian groups by
postcomposition. -/
def coefficientGradedPresheaf (X : DerivedCategory (SmoothRep.{u, u, u} R H)) (n p : ℤ) :
    (CompactOpenLevel (coefficientDomain e D))ᵒᵖ ⥤ AddCommGrpCat.{w} :=
  coefficientSmoothPresheaf R e ι ρ ⋙ singleFunctor _ 0 ⋙
    HyperextAbutment.gradedFunctor TStructure.t X n p

/-- The inclusion of the filtration step `F^p` into the abutment `Hom(X, A(K')[n])`, natural in
the level `K'`. -/
def coefficientFiltrationι (X : DerivedCategory (SmoothRep.{u, u, u} R H)) (n p : ℤ) :
    coefficientFiltrationPresheaf R e ι ρ X n p ⟶ coefficientAbutmentPresheaf R e ι ρ X n :=
  Functor.whiskerLeft (coefficientSmoothPresheaf R e ι ρ ⋙ singleFunctor _ 0)
    (HyperextAbutment.filtrationι TStructure.t X n p)

/-- The inclusion `F^q ⟶ F^p` of filtration steps for `p ≤ q`, natural in the level `K'`. -/
def coefficientFiltrationMapOfLE (X : DerivedCategory (SmoothRep.{u, u, u} R H)) (n : ℤ)
    {p q : ℤ} (hpq : p ≤ q) :
    coefficientFiltrationPresheaf R e ι ρ X n q ⟶ coefficientFiltrationPresheaf R e ι ρ X n p :=
  Functor.whiskerLeft (coefficientSmoothPresheaf R e ι ρ ⋙ singleFunctor _ 0)
    (HyperextAbutment.filtrationMapOfLE TStructure.t X n hpq)

/-- The projection `F^p ⟶ gr^p` of the abutment filtration, natural in the level `K'`. -/
def coefficientGradedπ (X : DerivedCategory (SmoothRep.{u, u, u} R H)) (n p : ℤ) :
    coefficientFiltrationPresheaf R e ι ρ X n p ⟶ coefficientGradedPresheaf R e ι ρ X n p :=
  Functor.whiskerLeft (coefficientSmoothPresheaf R e ι ρ ⋙ singleFunctor _ 0)
    (HyperextAbutment.gradedπ TStructure.t X n p)

end CoefficientExt

end Langlands.Shimura.EquivariantForms

namespace Langlands.Shimura.DefiniteForms

open CategoryTheory Opposite DerivedCategory
open Langlands.Global Langlands.Cohomology Langlands.Shimura.EquivariantForms
open Langlands.Shimura.CompactOpenLevel

universe u w t uR

section LocalCoefficients

variable {A : Type u} [Ring A] [Algebra ℚ A] (σ : AlgebraInvolution ℚ A) [Module.Finite ℚ A]
  (ℓ : FinitePlace ℚ) (Kℓ : Subgroup (σ.Points (FiniteCompletion ℚ ℓ)))

/-- The finite adelic points `g` whose `ℓ`-component `g_ℓ` lies in a subgroup `Kℓ` of the
`ℓ`-adic points. -/
def localCoefficientDomain : Subgroup σ.FiniteAdelicPoints :=
  Kℓ.comap (σ.finiteLocalMap ℓ).toMonoidHom

/-- The `ℓ`-component map `g ↦ g_ℓ` from `localCoefficientDomain σ ℓ Kℓ` to `Kℓ`. -/
def localCoefficientMap : localCoefficientDomain σ ℓ Kℓ →* Kℓ :=
  ((σ.finiteLocalMap ℓ).toMonoidHom.comp (localCoefficientDomain σ ℓ Kℓ).subtype).codRestrict Kℓ
    fun g => g.2

@[simp]
lemma localCoefficientMap_apply_coe (g : localCoefficientDomain σ ℓ Kℓ) :
    (localCoefficientMap σ ℓ Kℓ g : σ.Points (FiniteCompletion ℚ ℓ)) = σ.finiteLocalMap ℓ g :=
  rfl

variable {R : Type uR} [CommRing R] {V : Type t} [AddCommGroup V] [Module R V]
  (𝓛 : Representation R Kℓ V)

/-- A representation `𝓛` of `Kℓ` composed with the `ℓ`-component map `g ↦ g_ℓ`, as a
representation of `localCoefficientDomain σ ℓ Kℓ`. -/
abbrev localCoefficientRep : Representation R (localCoefficientDomain σ ℓ Kℓ) V :=
  𝓛.comp (localCoefficientMap σ ℓ Kℓ)

variable (p : ℕ) (hp : p ≠ 0)

/-- The elements `k` of `GJ(A_f^{(p)})` such that the `ℓ`-component of `e⁻¹ (1, k)` lies in
`Kℓ`, for the published splitting `e = σ.finiteAdelicPointsSplit p hp`. -/
abbrev dividingCoefficientDomain : Subgroup (σ.PrimeToPoints p) :=
  coefficientDomain (σ.finiteAdelicPointsSplit p hp) (localCoefficientDomain σ ℓ Kℓ)

/-- The `ℓ`-components of the level `e⁻¹ (1 × K')` lie in `Kℓ`, for a subgroup `K'` of
`dividingCoefficientDomain σ ℓ Kℓ p hp`. -/
lemma localLevel_awayLevel_le (K' : Subgroup (dividingCoefficientDomain σ ℓ Kℓ p hp)) :
    localLevel σ ℓ (awayLevel (σ.finiteAdelicPointsSplit p hp) (domainLevel _ K')) ≤ Kℓ :=
  Subgroup.map_le_iff_le_comap.2 (awayLevel_domainLevel_le _ K')

/-- The forms of level `e⁻¹ (1 × K')` with coefficients `𝓛` composed with the `ℓ`-component map
are Harris's `𝒜_ℓ(GJ, 𝓛, K)` (1999, (3.7)) for `K = e⁻¹ (1 × K')`. -/
lemma coefficientForms_eq_ellModuleForms (K' : Subgroup (dividingCoefficientDomain σ ℓ Kℓ p hp)) :
    coefficientForms R (σ.finiteAdelicPointsSplit p hp) σ.finiteAdelicDiagonal
        (localCoefficientRep σ ℓ Kℓ 𝓛) K' =
      ellModuleForms σ ℓ (awayLevel (σ.finiteAdelicPointsSplit p hp) (domainLevel _ K'))
        (𝓛.comp (Subgroup.inclusion (localLevel_awayLevel_le σ ℓ Kℓ p hp K'))) :=
  rfl

section Dividing

open scoped NumberField

variable {ℓ p}

/-- At a place `ℓ` whose prime ideal contains `p`, the `ℓ`-component of `e⁻¹ (1, k)` is
trivial. -/
lemma finiteLocalMap_awayHom (hℓ : (p : 𝓞 ℚ) ∈ ℓ.asIdeal) (k : σ.PrimeToPoints p) :
    σ.finiteLocalMap ℓ (awayHom (σ.finiteAdelicPointsSplit p hp) k) = 1 := by
  rw [← σ.dividingLocalMap_finiteAdelicPointsSplit p hp ⟨ℓ, hℓ⟩, awayHom_apply,
    ContinuousMulEquiv.apply_symm_apply]
  exact map_one _

/-- At a place `ℓ` whose prime ideal contains `p`, the coefficient domain is all of
`GJ(A_f^{(p)})`. -/
lemma dividingCoefficientDomain_eq_top (hℓ : (p : 𝓞 ℚ) ∈ ℓ.asIdeal) :
    dividingCoefficientDomain σ ℓ Kℓ p hp = ⊤ :=
  eq_top_iff.2 fun k _ => by
    change σ.finiteLocalMap ℓ (awayHom (σ.finiteAdelicPointsSplit p hp) k) ∈ Kℓ
    rw [finiteLocalMap_awayHom σ hp hℓ]
    exact one_mem Kℓ

/-- At a place `ℓ` whose prime ideal contains `p`, the coefficients act trivially: the forms of
level `e⁻¹ (1 × K')` with coefficients `𝓛` composed with the `ℓ`-component map are the forms
with trivial coefficients. -/
lemma coefficientForms_eq_awayLevelForms (hℓ : (p : 𝓞 ℚ) ∈ ℓ.asIdeal)
    (K' : Subgroup (dividingCoefficientDomain σ ℓ Kℓ p hp)) :
    coefficientForms R (σ.finiteAdelicPointsSplit p hp) σ.finiteAdelicDiagonal
        (localCoefficientRep σ ℓ Kℓ 𝓛) K' =
      awayLevelForms R (σ.finiteAdelicPointsSplit p hp) σ.finiteAdelicDiagonal V
        (domainLevel _ K') := by
  refine congrArg (forms σ.finiteAdelicDiagonal _) (MonoidHom.ext fun k => ?_)
  obtain ⟨a, -, ha⟩ := (mem_awayLevel (e := σ.finiteAdelicPointsSplit p hp)).1 k.2
  have h₁ : localCoefficientMap σ ℓ Kℓ
      (Subgroup.inclusion (awayLevel_domainLevel_le _ K') k) = 1 := by
    apply Subtype.ext
    rw [localCoefficientMap_apply_coe]
    change σ.finiteLocalMap ℓ (k : σ.FiniteAdelicPoints) = 1
    rw [← ha, finiteLocalMap_awayHom σ hp hℓ]
  change 𝓛 (localCoefficientMap σ ℓ Kℓ
    (Subgroup.inclusion (awayLevel_domainLevel_le _ K') k)) = 1
  rw [h₁, map_one]

end Dividing

end LocalCoefficients

section DividingExt

variable {A : Type u} [Ring A] [Algebra ℚ A] (σ : AlgebraInvolution ℚ A) [Module.Finite ℚ A]
  (ℓ : FinitePlace ℚ) (Kℓ : Subgroup (σ.Points (FiniteCompletion ℚ ℓ))) {R : Type u} [CommRing R]
  {V : Type u} [AddCommGroup V] [Module R V] (𝓛 : Representation R Kℓ V) (p : ℕ) (hp : p ≠ 0)

/-- Harris's smooth `GJ(ℚ_p)`-modules of forms with coefficients `𝓛`: the smooth part of right
translation by `GJ(∏_{v ∣ p} ℚ_v)` on the forms of level `e⁻¹ (1 × K')` with coefficients `𝓛`
composed with the `ℓ`-component map, for all compact open levels `K'` of
`dividingCoefficientDomain σ ℓ Kℓ p hp`, as a presheaf of smooth representations. -/
def dividingCoefficientSmoothPresheaf :
    (CompactOpenLevel (dividingCoefficientDomain σ ℓ Kℓ p hp))ᵒᵖ ⥤
      SmoothRep.{u, u, u} R (σ.DividingPoints p) :=
  coefficientSmoothPresheaf R (σ.finiteAdelicPointsSplit p hp) σ.finiteAdelicDiagonal
    (localCoefficientRep σ ℓ Kℓ 𝓛)

/-- The vectors of `dividingCoefficientSmoothPresheaf` at `K'` fixed by an open subgroup `U` of
`GJ(∏_{v ∣ p} ℚ_v)` are the forms of level `e⁻¹ (U × K')` whose coefficients are `𝓛` of the
`ℓ`-component of `e⁻¹ (1, (e k).2)`. -/
def dividingCoefficientSmoothFixedEquiv
    (K' : CompactOpenLevel (dividingCoefficientDomain σ ℓ Kℓ p hp))
    (U : OpenSubgroup (σ.DividingPoints p)) :
    fixedVectors (V := smoothVectors (coefficientTranslation R (σ.finiteAdelicPointsSplit p hp)
        σ.finiteAdelicDiagonal (localCoefficientRep σ ℓ Kℓ 𝓛) K'.subgroup))
      (smoothPart (coefficientTranslation R (σ.finiteAdelicPointsSplit p hp)
        σ.finiteAdelicDiagonal (localCoefficientRep σ ℓ Kℓ 𝓛) K'.subgroup)) U.toSubgroup ≃ₗ[R]
      forms σ.finiteAdelicDiagonal
        (splitLevel (σ.finiteAdelicPointsSplit p hp) U (domainLevel _ K'.subgroup))
        ((localCoefficientRep σ ℓ Kℓ 𝓛).comp
          (splitCoefficientHom (σ.finiteAdelicPointsSplit p hp) U K'.subgroup)) :=
  coefficientSmoothFixedEquiv R _ _ _ K'.subgroup U

/-- `Ext^i(W, -)` in smooth representations of `GJ(∏_{v ∣ p} ℚ_v)` of the forms of
`dividingCoefficientSmoothPresheaf`, as a presheaf of `R`-modules. -/
def dividingCoefficientExtPresheaf (W : SmoothRep.{u, u, u} R (σ.DividingPoints p)) (i : ℕ) :
    (CompactOpenLevel (dividingCoefficientDomain σ ℓ Kℓ p hp))ᵒᵖ ⥤ ModuleCat.{u} R :=
  coefficientExtPresheaf R (σ.finiteAdelicPointsSplit p hp) σ.finiteAdelicDiagonal
    (localCoefficientRep σ ℓ Kℓ 𝓛) W i

variable [HasDerivedCategory.{w} (SmoothRep.{u, u, u} R (σ.DividingPoints p))]

/-- The hyperext spectral sequence of an object `X` of the derived category of smooth
representations of `GJ(∏_{v ∣ p} ℚ_v)` and the forms of `dividingCoefficientSmoothPresheaf` at
`K'` placed in degree `0`. -/
def dividingCoefficientSpectralSequence
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p)))
    (K' : CompactOpenLevel (dividingCoefficientDomain σ ℓ Kℓ p hp)) :
    E₂CohomologicalSpectralSequence AddCommGrpCat.{w} :=
  coefficientSpectralSequence R (σ.finiteAdelicPointsSplit p hp) σ.finiteAdelicDiagonal
    (localCoefficientRep σ ℓ Kℓ 𝓛) X K'

/-- The object in position `(i, j)` on page 2 of `dividingCoefficientSpectralSequence X K'` is
`Ext^i(H^{-j}(X), -)` of the forms of `dividingCoefficientSmoothPresheaf` at `K'`. -/
def dividingCoefficientSecondPageAddEquiv
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p)))
    (K' : CompactOpenLevel (dividingCoefficientDomain σ ℓ Kℓ p hp)) (i : ℕ) (j : ℤ) :
    ((dividingCoefficientSpectralSequence σ ℓ Kℓ 𝓛 p hp X K').page 2).X ⟨i, j⟩ ≃+
      (dividingCoefficientExtPresheaf σ ℓ Kℓ 𝓛 p hp ((homologyFunctor _ (-j)).obj X) i).obj
        (op K') :=
  coefficientSecondPageAddEquiv R _ _ _ X K' i j

/-- The intended abutment `Hom(X, A(K')[n])` in total degree `n`, for the forms `A(K')` of
`dividingCoefficientSmoothPresheaf` at `K'` placed in degree `0`, as a presheaf of abelian
groups. -/
def dividingCoefficientAbutmentPresheaf
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n : ℤ) :
    (CompactOpenLevel (dividingCoefficientDomain σ ℓ Kℓ p hp))ᵒᵖ ⥤ AddCommGrpCat.{w} :=
  coefficientAbutmentPresheaf R (σ.finiteAdelicPointsSplit p hp) σ.finiteAdelicDiagonal
    (localCoefficientRep σ ℓ Kℓ 𝓛) X n

/-- The term of the spectral object of `dividingCoefficientSpectralSequence X K'` in degree `n`
for the arrow `⊥ ⟶ ⊤` is the value at `K'` of `dividingCoefficientAbutmentPresheaf X n`. -/
def dividingCoefficientAbutmentIso
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p)))
    (K' : CompactOpenLevel (dividingCoefficientDomain σ ℓ Kℓ p hp)) (n : ℤ) :
    ((HyperextSpectralSequence.hyperextSpectralObject TStructure.t X
        ((singleFunctor _ 0).obj
          ((dividingCoefficientSmoothPresheaf σ ℓ Kℓ 𝓛 p hp).obj (op K')))).H n).obj
        (ComposableArrows.mk₁ (homOfLE (show (⊥ : EInt) ≤ ⊤ from bot_le))) ≅
      (dividingCoefficientAbutmentPresheaf σ ℓ Kℓ 𝓛 p hp X n).obj (op K') :=
  coefficientAbutmentIso R _ _ _ X K' n

/-- The step `F^i` of the abutment filtration on `Hom(X, A(K')[n])`, as a presheaf of abelian
groups. -/
def dividingCoefficientFiltrationPresheaf
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n i : ℤ) :
    (CompactOpenLevel (dividingCoefficientDomain σ ℓ Kℓ p hp))ᵒᵖ ⥤ AddCommGrpCat.{w} :=
  coefficientFiltrationPresheaf R (σ.finiteAdelicPointsSplit p hp) σ.finiteAdelicDiagonal
    (localCoefficientRep σ ℓ Kℓ 𝓛) X n i

/-- The graded piece `gr^i = F^i / F^{i+1}` of the abutment filtration on `Hom(X, A(K')[n])`, as
a presheaf of abelian groups. -/
def dividingCoefficientGradedPresheaf
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n i : ℤ) :
    (CompactOpenLevel (dividingCoefficientDomain σ ℓ Kℓ p hp))ᵒᵖ ⥤ AddCommGrpCat.{w} :=
  coefficientGradedPresheaf R (σ.finiteAdelicPointsSplit p hp) σ.finiteAdelicDiagonal
    (localCoefficientRep σ ℓ Kℓ 𝓛) X n i

/-- The inclusion of the filtration step `F^i` into the abutment `Hom(X, A(K')[n])`, natural in
the level `K'`. -/
def dividingCoefficientFiltrationι
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n i : ℤ) :
    dividingCoefficientFiltrationPresheaf σ ℓ Kℓ 𝓛 p hp X n i ⟶
      dividingCoefficientAbutmentPresheaf σ ℓ Kℓ 𝓛 p hp X n :=
  coefficientFiltrationι R _ _ _ X n i

/-- The inclusion `F^j ⟶ F^i` of filtration steps for `i ≤ j`, natural in the level `K'`. -/
def dividingCoefficientFiltrationMapOfLE
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n : ℤ) {i j : ℤ}
    (hij : i ≤ j) :
    dividingCoefficientFiltrationPresheaf σ ℓ Kℓ 𝓛 p hp X n j ⟶
      dividingCoefficientFiltrationPresheaf σ ℓ Kℓ 𝓛 p hp X n i :=
  coefficientFiltrationMapOfLE R _ _ _ X n hij

/-- The projection `F^i ⟶ gr^i` of the abutment filtration, natural in the level `K'`. -/
def dividingCoefficientGradedπ
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n i : ℤ) :
    dividingCoefficientFiltrationPresheaf σ ℓ Kℓ 𝓛 p hp X n i ⟶
      dividingCoefficientGradedPresheaf σ ℓ Kℓ 𝓛 p hp X n i :=
  coefficientGradedπ R _ _ _ X n i

end DividingExt

end Langlands.Shimura.DefiniteForms
