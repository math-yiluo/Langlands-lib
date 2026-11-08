import Langlands.Shimura.EquivariantForms
import Langlands.Shimura.SplitLevelTower
import Langlands.Shimura.Unitary.PointsSplit
import Langlands.Cohomology.SmoothHyperextSecondPage
import Langlands.Representation.Smooth.SmoothPart.FixedVectorsDefinitions
import Langlands.Cohomology.HyperextAbutmentNaturality

/-!
# Forms with trivial coefficients as smooth representations of one factor, and their Ext

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, 1999, p.309,
Proposition 4.4, gives a spectral sequence of `𝒪_m`-modules
`E₂^{i,j} = Ext^i(H_c^{2(n-1)-j}(M̌_N, 𝒪_m(n-1)), 𝒜_ℓ(GJ, 𝓛, K(m))) ⇒ H^{i+j}(S̄_{K(N,m)}, 𝓛~)`
for a free `𝒪/ℓ^m 𝒪`-module `𝓛` with constant étale sheaf `𝓛~`, where "`Ext^i` denotes the
`i`-th derived functor of `Hom` in the category of smooth `𝒪_m[GJ]`-modules", and "as
`K(N,m)^p` varies the spectral sequences are `GG(𝔸_f^p)`-equivariant". This file constructs the
smooth `GJ_p`-module of forms in the second argument, the `Ext` groups, the hyperext spectral
sequence with its second page and abutment, and their variation with the level away from `p`.
It does not construct `M̌_N`, its cohomology, or the Shimura variety, and does not prove
convergence or the comparison with `H^{i+j}(S̄_{K(N,m)}, 𝓛~)`.

## Main definitions

For groups `Γ`, `G` with `ι : Γ →* G` and an isomorphism of topological groups
`e : G ≃ₜ* H × H'`, in the namespace `EquivariantForms`:

* `awayLevelForms R e ι V K'`: the functions `f : G → V` with `f (ι γ * g) = f g` and
  `f (g * k) = f g` for `k ∈ e⁻¹ (1 × K')`, with right translation `factorTranslation` by `H`
  and right translation `awayTranslate` by `H'` between levels.
* `factorFixedEquiv`: the vectors fixed by `U ≤ H` are the forms of level `e⁻¹ (U × K')`
  (`splitLevel e U K'`); `factorSmoothFixedEquiv` for the smooth part.
* `factorFormsPresheaf`, `factorSmoothPresheaf`: the presheaves `K' ↦ awayLevelForms` of
  representations and of smooth representations of `H` on compact open levels `K'` of `H'`.
* `factorExtPresheaf W i`: `K' ↦ Ext^i(W, smooth part of awayLevelForms K')`.
* `factorSpectralSequence X K'`, `factorSecondPageAddEquiv`: the published hyperext spectral
  sequence of `X` and the smooth forms of level `e⁻¹ (1 × K')`, whose second page in position
  `(i, j)` is `Ext^i(H^{-j}(X), -)` of these forms.
* `factorAbutmentPresheaf`, `factorAbutmentIso`, `factorFiltrationPresheaf`,
  `factorGradedPresheaf`: the intended abutment `Hom(X, A(K')[n])`, its filtration steps and
  graded pieces as presheaves on the levels `K'`.

In the namespace `DefiniteForms`, for `σ : AlgebraInvolution ℚ A`, `p ≠ 0` and the published
splitting `σ.finiteAdelicPointsSplit p hp : GJ(𝔸_f) ≃ₜ* GJ(∏_{v ∣ p} ℚ_v) × GJ(𝔸_f^{(p)})`:
`dividingSmoothPresheaf`, `dividingSmoothFixedEquiv`, `dividingExtPresheaf`,
`dividingSpectralSequence`, `dividingSecondPageAddEquiv`, `dividingAbutmentPresheaf`,
`dividingAbutmentIso`, `dividingFiltrationPresheaf` and `dividingGradedPresheaf`.
-/

noncomputable section

namespace Langlands.Shimura.EquivariantForms

open CategoryTheory CategoryTheory.Limits Opposite DerivedCategory
open Langlands.Cohomology Langlands.Shimura.CompactOpenLevel

universe t uR uΓ uG uH uH' u w

section Split

variable (R : Type uR) [CommRing R] {Γ : Type uΓ} {G : Type uG} {H : Type uH} {H' : Type uH'}
  [Group Γ] [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] [Group H']
  [TopologicalSpace H'] (e : G ≃ₜ* H × H') (ι : Γ →* G) (V : Type t) [AddCommGroup V]
  [Module R V]

/-- The subgroup `e⁻¹ (1 × K')` of `G`, for a subgroup `K'` of the second factor `H'`. -/
def awayLevel (K' : Subgroup H') : Subgroup G :=
  K'.map (awayHom e)

variable {e} in
lemma mem_awayLevel {K' : Subgroup H'} {g : G} :
    g ∈ awayLevel e K' ↔ ∃ k ∈ K', awayHom e k = g :=
  Subgroup.mem_map

lemma awayHom_mem_awayLevel {K' : Subgroup H'} {k : H'} (hk : k ∈ K') :
    awayHom e k ∈ awayLevel e K' :=
  Subgroup.mem_map_of_mem _ hk

/-- The image of the first factor commutes elementwise with `e⁻¹ (1 × K')`. -/
lemma factorHom_mul_awayLevel (K' : Subgroup H') (h : H) (k : awayLevel e K') :
    factorHom e h * k = k * factorHom e h := by
  obtain ⟨a, -, ha⟩ := (mem_awayLevel (e := e)).1 k.2
  rw [← ha]
  exact (factorHom_commute_awayHom e h a).eq

/-- The subgroup `e⁻¹ (U × K')` of `G`. -/
def splitLevel (U : Subgroup H) (K' : Subgroup H') : Subgroup G :=
  (U.prod K').comap (e : G →* H × H')

variable {e} in
lemma mem_splitLevel {U : Subgroup H} {K' : Subgroup H'} {g : G} :
    g ∈ splitLevel e U K' ↔ (e g).1 ∈ U ∧ (e g).2 ∈ K' :=
  Iff.rfl

lemma factorHom_mem_splitLevel {U : Subgroup H} (K' : Subgroup H') {h : H} (hh : h ∈ U) :
    factorHom e h ∈ splitLevel e U K' := by
  rw [mem_splitLevel, factorHom_apply, e.apply_symm_apply]
  exact ⟨hh, K'.one_mem⟩

lemma awayLevel_le_splitLevel (U : Subgroup H) (K' : Subgroup H') :
    awayLevel e K' ≤ splitLevel e U K' := by
  intro g hg
  obtain ⟨a, ha, rfl⟩ := (mem_awayLevel (e := e)).1 hg
  rw [mem_splitLevel, awayHom_apply, e.apply_symm_apply]
  exact ⟨U.one_mem, ha⟩

/-- Forms of level `e⁻¹ (1 × K')` with trivial coefficients `V`: the functions `f : G → V` with
`f (ι γ * g) = f g` and `f (g * k) = f g` for `k ∈ e⁻¹ (1 × K')`. -/
abbrev awayLevelForms (K' : Subgroup H') : Submodule R (G → V) :=
  forms ι (awayLevel e K') (Representation.trivial R (awayLevel e K') V)

/-- Right translation `(h • f) g = f (g * e⁻¹ (h, 1))` by the first factor `H` on the forms of
level `e⁻¹ (1 × K')`: the published `rightTranslation` along `factorHom e`. -/
def factorTranslation (K' : Subgroup H') :
    Representation R H (awayLevelForms R e ι V K') :=
  rightTranslation ι _ _ (factorHom e) (factorHom_mul_awayLevel e K')

@[simp]
lemma factorTranslation_apply_coe (K' : Subgroup H') (h : H) (f : awayLevelForms R e ι V K')
    (g : G) : (factorTranslation R e ι V K' h f).1 g = f.1 (g * factorHom e h) :=
  rfl

/-- Right translation `f ↦ (x ↦ f (x * e⁻¹ (1, g)))` from level `e⁻¹ (1 × L)` to level
`e⁻¹ (1 × K)`, for `g : H'` with `g⁻¹ * k * g ∈ L` for all `k ∈ K`. -/
def awayTranslate {K L : Subgroup H'} (g : H') (hg : ∀ k ∈ K, g⁻¹ * k * g ∈ L) :
    awayLevelForms R e ι V L →ₗ[R] awayLevelForms R e ι V K :=
  (LinearMap.funLeft R V (· * awayHom e g)).restrict fun f hf =>
    ⟨fun γ x => by
      change f (ι γ * x * awayHom e g) = f (x * awayHom e g)
      rw [mul_assoc]
      exact hf.1 γ _, fun x k => by
      obtain ⟨a, ha, hak⟩ := (mem_awayLevel (e := e)).1 k.2
      have hx : x * k * awayHom e g = x * awayHom e g *
          ((⟨awayHom e (g⁻¹ * a * g), awayHom_mem_awayLevel e (hg a ha)⟩ : awayLevel e L) : G) := by
        rw [← hak, mul_assoc, mul_assoc, ← map_mul, ← map_mul]
        congr 2
        group
      change f (x * k * awayHom e g) = f (x * awayHom e g)
      rw [hx, hf.2]
      rfl⟩

@[simp]
lemma awayTranslate_apply_coe {K L : Subgroup H'} (g : H') (hg : ∀ k ∈ K, g⁻¹ * k * g ∈ L)
    (f : awayLevelForms R e ι V L) (x : G) :
    (awayTranslate R e ι V g hg f).1 x = f.1 (x * awayHom e g) :=
  rfl

/-- Right translation by the second factor commutes with right translation by the first. -/
def awayTranslateIntertwining {K L : Subgroup H'} (g : H') (hg : ∀ k ∈ K, g⁻¹ * k * g ∈ L) :
    (factorTranslation R e ι V L).IntertwiningMap (factorTranslation R e ι V K) where
  toLinearMap := awayTranslate R e ι V g hg
  isIntertwining' h := by
    ext f x
    change f.1 (x * awayHom e g * factorHom e h) = f.1 (x * factorHom e h * awayHom e g)
    rw [mul_assoc, mul_assoc, (factorHom_commute_awayHom e h g).eq]

/-- The forms of level `e⁻¹ (1 × K')` with right translation by `H`, for all compact open levels
`K'` of `H'`, as a presheaf on the category of levels of `H'` with right translation
`awayTranslate` on arrows. -/
def factorFormsPresheaf : (CompactOpenLevel H')ᵒᵖ ⥤ Rep.{max uG t} R H where
  obj K' := Rep.of (factorTranslation R e ι V K'.unop.subgroup)
  map a := Rep.ofHom (awayTranslateIntertwining R e ι V a.unop.element a.unop.respects)
  map_id K' := by
    ext f x
    change f.1 (x * awayHom e 1) = f.1 x
    rw [map_one, mul_one]
  map_comp a b := by
    ext f x
    change f.1 (x * awayHom e (_ * _)) = f.1 (x * awayHom e _ * awayHom e _)
    rw [map_mul, mul_assoc]

/-- The vectors of `factorTranslation` fixed by a subgroup `U` of `H` are the forms of level
`e⁻¹ (U × K')`: every `k ∈ e⁻¹ (U × K')` is `e⁻¹ ((e k).1, 1) * e⁻¹ (1, (e k).2)`. -/
def factorFixedEquiv (K' : Subgroup H') (U : Subgroup H) :
    fixedVectors (factorTranslation R e ι V K') U ≃ₗ[R]
      forms ι (splitLevel e U K') (Representation.trivial R (splitLevel e U K') V) where
  toFun f := ⟨f.1.1, f.1.2.1, fun g k => by
      obtain ⟨hk₁, hk₂⟩ := mem_splitLevel.1 k.2
      have h₁ := f.1.2.2 (g * factorHom e (e k).1)
        ⟨awayHom e (e k).2, awayHom_mem_awayLevel e hk₂⟩
      have h₂ := congrArg (fun f' : awayLevelForms R e ι V K' => f'.1 g) (f.2 ⟨(e k).1, hk₁⟩)
      change f.1.1 (g * factorHom e (e k).1 * awayHom e (e k).2) =
        f.1.1 (g * factorHom e (e k).1) at h₁
      change f.1.1 (g * factorHom e (e k).1) = f.1.1 g at h₂
      change f.1.1 (g * k) = f.1.1 g
      rw [← factorHom_mul_awayHom e (k : G), ← mul_assoc, h₁, h₂]⟩
  invFun f := ⟨⟨f.1, f.2.1, fun g k => f.2.2 g ⟨k, awayLevel_le_splitLevel e U K' k.2⟩⟩,
    fun u => Subtype.ext (funext fun g => f.2.2 g ⟨_, factorHom_mem_splitLevel e K' u.2⟩)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
lemma factorFixedEquiv_apply_coe (K' : Subgroup H') (U : Subgroup H)
    (f : fixedVectors (factorTranslation R e ι V K') U) :
    (factorFixedEquiv R e ι V K' U f).1 = f.1.1 :=
  rfl

/-- A form of level `e⁻¹ (1 × K')` is a smooth vector for right translation by `H` if and only if
it is a form of level `e⁻¹ (U × K')` for some open subgroup `U` of `H`. -/
lemma isSmoothVector_factorTranslation_iff (K' : Subgroup H') (f : awayLevelForms R e ι V K') :
    IsSmoothVector (factorTranslation R e ι V K') f ↔
      ∃ U : OpenSubgroup H, f.1 ∈ forms ι (splitLevel e U K')
        (Representation.trivial R (splitLevel e U K') V) :=
  exists_congr fun U => ⟨fun hf => (factorFixedEquiv R e ι V K' U ⟨f, hf⟩).2,
    fun hf => ((factorFixedEquiv R e ι V K' U).symm ⟨f.1, hf⟩).2⟩

/-- For compact open levels, `e⁻¹ (U × K')` is the published level
`transport e.symm (prod U K')`. -/
lemma splitLevel_eq_transport (U : CompactOpenLevel H) (K' : CompactOpenLevel H') :
    splitLevel e U.subgroup K'.subgroup =
      (CompactOpenLevel.transport e.symm (CompactOpenLevel.prod U K')).subgroup :=
  Subgroup.ext fun _ => Iff.rfl

variable [IsTopologicalGroup H]

/-- The smooth part of `factorTranslation`, for all compact open levels `K'` of `H'`: a
presheaf of smooth representations of `H`. -/
def factorSmoothPresheaf : (CompactOpenLevel H')ᵒᵖ ⥤ SmoothRep.{uR, uH, max uG t} R H :=
  factorFormsPresheaf R e ι V ⋙ SmoothRep.smoothPartFunctor.{uR, uH, max uG t} R H

/-- The vectors of the smooth part of `factorTranslation` fixed by an open subgroup `U` of `H`
are the forms of level `e⁻¹ (U × K')`. -/
def factorSmoothFixedEquiv (K' : Subgroup H') (U : OpenSubgroup H) :
    fixedVectors (V := smoothVectors (factorTranslation R e ι V K'))
      (smoothPart (factorTranslation R e ι V K')) U.toSubgroup ≃ₗ[R]
      forms ι (splitLevel e U K') (Representation.trivial R (splitLevel e U K') V) :=
  (smoothPartFixedVectorsEquiv _ U).trans (factorFixedEquiv R e ι V K' U)

@[simp]
lemma factorSmoothFixedEquiv_apply_coe (K' : Subgroup H') (U : OpenSubgroup H)
    (f : fixedVectors (V := smoothVectors (factorTranslation R e ι V K'))
      (smoothPart (factorTranslation R e ι V K')) U.toSubgroup) :
    (factorSmoothFixedEquiv R e ι V K' U f).1 = f.1.1.1 :=
  rfl

end Split

section Ext

variable (R : Type u) [CommRing R] {Γ : Type uΓ} {G : Type u} {H : Type u} {H' : Type uH'}
  [Group Γ] [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Group H'] [TopologicalSpace H'] (e : G ≃ₜ* H × H') (ι : Γ →* G) (V : Type u)
  [AddCommGroup V] [Module R V]

/-- `Ext^i(W, -)` in smooth representations of `H` of the smooth forms of level `e⁻¹ (1 × K')`,
for all compact open levels `K'` of `H'`, as a presheaf of `R`-modules. -/
def factorExtPresheaf (W : SmoothRep.{u, u, u} R H) (i : ℕ) :
    (CompactOpenLevel H')ᵒᵖ ⥤ ModuleCat.{u} R :=
  factorSmoothPresheaf R e ι V ⋙ SmoothExt.ext R H W i

variable [HasDerivedCategory.{w} (SmoothRep.{u, u, u} R H)]

/-- The hyperext spectral sequence of an object `X` of the derived category of smooth
representations of `H` and the smooth forms of level `e⁻¹ (1 × K')` placed in degree `0`. -/
def factorSpectralSequence (X : DerivedCategory (SmoothRep.{u, u, u} R H))
    (K' : CompactOpenLevel H') : E₂CohomologicalSpectralSequence AddCommGrpCat.{w} :=
  HyperextSpectralSequence.hyperextSpectralSequence TStructure.t X
    ((singleFunctor _ 0).obj ((factorSmoothPresheaf R e ι V).obj (op K')))

/-- The object in position `(p, q)` on page 2 of `factorSpectralSequence X K'` is
`Ext^p(H^{-q}(X), -)` of the smooth forms of level `e⁻¹ (1 × K')`. -/
def factorSecondPageAddEquiv (X : DerivedCategory (SmoothRep.{u, u, u} R H))
    (K' : CompactOpenLevel H') (p : ℕ) (q : ℤ) :
    ((factorSpectralSequence R e ι V X K').page 2).X ⟨p, q⟩ ≃+
      (factorExtPresheaf R e ι V ((homologyFunctor _ (-q)).obj X) p).obj (op K') :=
  SmoothHyperext.secondPageAddEquiv R H X _ p q

/-- The intended abutment `Hom(X, A(K')[n])` in total degree `n`, for the smooth forms `A(K')` of
level `e⁻¹ (1 × K')` placed in degree `0`, as a presheaf of abelian groups on compact open
levels `K'` of `H'`. -/
def factorAbutmentPresheaf (X : DerivedCategory (SmoothRep.{u, u, u} R H)) (n : ℤ) :
    (CompactOpenLevel H')ᵒᵖ ⥤ AddCommGrpCat.{w} :=
  factorSmoothPresheaf R e ι V ⋙ singleFunctor _ 0 ⋙ shiftFunctor _ n ⋙
    preadditiveCoyoneda.obj (op X)

/-- The term of the spectral object of `factorSpectralSequence X K'` in degree `n` for the arrow
`⊥ ⟶ ⊤` is the value at `K'` of `factorAbutmentPresheaf X n`. -/
def factorAbutmentIso (X : DerivedCategory (SmoothRep.{u, u, u} R H))
    (K' : CompactOpenLevel H') (n : ℤ) :
    ((HyperextSpectralSequence.hyperextSpectralObject TStructure.t X
        ((singleFunctor _ 0).obj ((factorSmoothPresheaf R e ι V).obj (op K')))).H n).obj
        (ComposableArrows.mk₁ (homOfLE (show (⊥ : EInt) ≤ ⊤ from bot_le))) ≅
      (factorAbutmentPresheaf R e ι V X n).obj (op K') :=
  HyperextSpectralSequence.abutmentIso _ _ _ n

/-- The step `F^p` of the abutment filtration on `Hom(X, A(K')[n])`, for all compact open levels
`K'` of `H'`, as a presheaf of abelian groups by postcomposition. -/
def factorFiltrationPresheaf (X : DerivedCategory (SmoothRep.{u, u, u} R H)) (n p : ℤ) :
    (CompactOpenLevel H')ᵒᵖ ⥤ AddCommGrpCat.{w} where
  obj K' := AddCommGrpCat.of (HyperextAbutment.filtration TStructure.t X
    ((singleFunctor _ 0).obj ((factorSmoothPresheaf R e ι V).obj K')) n p)
  map a := AddCommGrpCat.ofHom (HyperextAbutment.filtrationPostcomp TStructure.t X
    ((singleFunctor _ 0).map ((factorSmoothPresheaf R e ι V).map a)) n p)
  map_id K' := by
    ext : 1
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
      HyperextAbutment.filtrationPostcomp_id]
    rfl
  map_comp a b := by
    ext : 1
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      HyperextAbutment.filtrationPostcomp_comp]
    rfl

/-- The graded piece `gr^p = F^p / F^{p+1}` of the abutment filtration on `Hom(X, A(K')[n])`,
for all compact open levels `K'` of `H'`, as a presheaf of abelian groups by postcomposition. -/
def factorGradedPresheaf (X : DerivedCategory (SmoothRep.{u, u, u} R H)) (n p : ℤ) :
    (CompactOpenLevel H')ᵒᵖ ⥤ AddCommGrpCat.{w} where
  obj K' := AddCommGrpCat.of (HyperextAbutment.graded TStructure.t X
    ((singleFunctor _ 0).obj ((factorSmoothPresheaf R e ι V).obj K')) n p)
  map a := AddCommGrpCat.ofHom (HyperextAbutment.gradedPostcomp TStructure.t X
    ((singleFunctor _ 0).map ((factorSmoothPresheaf R e ι V).map a)) n p)
  map_id K' := by
    ext : 1
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
      HyperextAbutment.gradedPostcomp_id]
    rfl
  map_comp a b := by
    ext : 1
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      HyperextAbutment.gradedPostcomp_comp]
    rfl

end Ext

end Langlands.Shimura.EquivariantForms

namespace Langlands.Shimura.DefiniteForms

open CategoryTheory Opposite DerivedCategory
open Langlands.Cohomology Langlands.Shimura.EquivariantForms

universe u w

variable {A : Type u} [Ring A] [Algebra ℚ A] (σ : AlgebraInvolution ℚ A) [Module.Finite ℚ A]
  (p : ℕ) (hp : p ≠ 0) (R : Type u) [CommRing R] (V : Type u) [AddCommGroup V] [Module R V]

/-- Harris's smooth `GJ(ℚ_p)`-modules of forms with trivial coefficients `V`: the smooth part of
right translation by `GJ(∏_{v ∣ p} ℚ_v)` on the functions `GJ(ℚ) \ GJ(A_f) / (1 × K') → V`, for
all compact open levels `K'` of `GJ(A_f^{(p)})`, as a presheaf of smooth representations. -/
def dividingSmoothPresheaf :
    (CompactOpenLevel (σ.PrimeToPoints p))ᵒᵖ ⥤ SmoothRep.{u, u, u} R (σ.DividingPoints p) :=
  factorSmoothPresheaf R (σ.finiteAdelicPointsSplit p hp) σ.finiteAdelicDiagonal V

/-- The vectors of `dividingSmoothPresheaf` at `K'` fixed by an open subgroup `U` of
`GJ(∏_{v ∣ p} ℚ_v)` are the forms of level `U × K'` with trivial coefficients `V`. -/
def dividingSmoothFixedEquiv (K' : CompactOpenLevel (σ.PrimeToPoints p))
    (U : OpenSubgroup (σ.DividingPoints p)) :
    fixedVectors (V := smoothVectors (factorTranslation R (σ.finiteAdelicPointsSplit p hp)
        σ.finiteAdelicDiagonal V K'.subgroup))
      (smoothPart (factorTranslation R (σ.finiteAdelicPointsSplit p hp) σ.finiteAdelicDiagonal V
        K'.subgroup)) U.toSubgroup ≃ₗ[R]
      forms σ.finiteAdelicDiagonal (splitLevel (σ.finiteAdelicPointsSplit p hp) U K'.subgroup)
        (Representation.trivial R (splitLevel (σ.finiteAdelicPointsSplit p hp) U K'.subgroup) V) :=
  factorSmoothFixedEquiv R _ _ V K'.subgroup U

/-- `Ext^i(W, -)` in smooth representations of `GJ(∏_{v ∣ p} ℚ_v)` of the forms of
`dividingSmoothPresheaf`, as a presheaf of `R`-modules on compact open levels of
`GJ(A_f^{(p)})`. -/
def dividingExtPresheaf (W : SmoothRep.{u, u, u} R (σ.DividingPoints p)) (i : ℕ) :
    (CompactOpenLevel (σ.PrimeToPoints p))ᵒᵖ ⥤ ModuleCat.{u} R :=
  factorExtPresheaf R (σ.finiteAdelicPointsSplit p hp) σ.finiteAdelicDiagonal V W i

variable [HasDerivedCategory.{w} (SmoothRep.{u, u, u} R (σ.DividingPoints p))]

/-- The hyperext spectral sequence of an object `X` of the derived category of smooth
representations of `GJ(∏_{v ∣ p} ℚ_v)` and the forms of `dividingSmoothPresheaf` at `K'` placed
in degree `0`. -/
def dividingSpectralSequence (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p)))
    (K' : CompactOpenLevel (σ.PrimeToPoints p)) :
    E₂CohomologicalSpectralSequence AddCommGrpCat.{w} :=
  factorSpectralSequence R (σ.finiteAdelicPointsSplit p hp) σ.finiteAdelicDiagonal V X K'

/-- The object in position `(i, j)` on page 2 of `dividingSpectralSequence X K'` is
`Ext^i(H^{-j}(X), -)` of the forms of `dividingSmoothPresheaf` at `K'`. -/
def dividingSecondPageAddEquiv
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p)))
    (K' : CompactOpenLevel (σ.PrimeToPoints p)) (i : ℕ) (j : ℤ) :
    ((dividingSpectralSequence σ p hp R V X K').page 2).X ⟨i, j⟩ ≃+
      (dividingExtPresheaf σ p hp R V ((homologyFunctor _ (-j)).obj X) i).obj (op K') :=
  factorSecondPageAddEquiv R _ _ V X K' i j

/-- The intended abutment `Hom(X, A(K')[n])` in total degree `n`, for the forms `A(K')` of
`dividingSmoothPresheaf` at `K'` placed in degree `0`, as a presheaf of abelian groups on compact
open levels `K'` of `GJ(A_f^{(p)})`. -/
def dividingAbutmentPresheaf
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n : ℤ) :
    (CompactOpenLevel (σ.PrimeToPoints p))ᵒᵖ ⥤ AddCommGrpCat.{w} :=
  factorAbutmentPresheaf R (σ.finiteAdelicPointsSplit p hp) σ.finiteAdelicDiagonal V X n

/-- The term of the spectral object of `dividingSpectralSequence X K'` in degree `n` for the
arrow `⊥ ⟶ ⊤` is the value at `K'` of `dividingAbutmentPresheaf X n`. -/
def dividingAbutmentIso (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p)))
    (K' : CompactOpenLevel (σ.PrimeToPoints p)) (n : ℤ) :
    ((HyperextSpectralSequence.hyperextSpectralObject TStructure.t X
        ((singleFunctor _ 0).obj ((dividingSmoothPresheaf σ p hp R V).obj (op K')))).H n).obj
        (ComposableArrows.mk₁ (homOfLE (show (⊥ : EInt) ≤ ⊤ from bot_le))) ≅
      (dividingAbutmentPresheaf σ p hp R V X n).obj (op K') :=
  factorAbutmentIso R _ _ V X K' n

/-- The step `F^i` of the abutment filtration on `Hom(X, A(K')[n])`, as a presheaf of abelian
groups on compact open levels `K'` of `GJ(A_f^{(p)})`. -/
def dividingFiltrationPresheaf
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n i : ℤ) :
    (CompactOpenLevel (σ.PrimeToPoints p))ᵒᵖ ⥤ AddCommGrpCat.{w} :=
  factorFiltrationPresheaf R (σ.finiteAdelicPointsSplit p hp) σ.finiteAdelicDiagonal V X n i

/-- The graded piece `gr^i = F^i / F^{i+1}` of the abutment filtration on `Hom(X, A(K')[n])`, as
a presheaf of abelian groups on compact open levels `K'` of `GJ(A_f^{(p)})`. -/
def dividingGradedPresheaf
    (X : DerivedCategory (SmoothRep.{u, u, u} R (σ.DividingPoints p))) (n i : ℤ) :
    (CompactOpenLevel (σ.PrimeToPoints p))ᵒᵖ ⥤ AddCommGrpCat.{w} :=
  factorGradedPresheaf R (σ.finiteAdelicPointsSplit p hp) σ.finiteAdelicDiagonal V X n i

end Langlands.Shimura.DefiniteForms
