/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit
public import WeilConjectures.AlgebraicGeometry.Sites.Hilbert90Etale
public import WeilConjectures.AlgebraicGeometry.Sites.PointFunctions
public import WeilConjectures.CategoryTheory.Sites.CechCriterion
public import WeilConjectures.FieldTheory.Galois.CrossedProduct

/-!
# The Čech complex of a Galois covering of the spectrum of a field

Let `M / K` be a finite Galois extension with group `G` and consider the covering
`Spec M ⟶ Spec K` of the small étale site of `Spec K`. Its Čech nerve has in degree `k` the
`(k + 1)`-fold fibre product `N_k = Spec M ×_K ⋯ ×_K Spec M`. For every `g : G^{k + 1}` the
morphisms `Spec(g l) : Spec M ⟶ Spec M` define a section `s g : Spec M ⟶ N_k`, and these
sections cover `N_k`: a point of `N_k` with residue field `E` is given by `k + 1` embeddings
`M → E`, which differ by elements of `G` as `M / K` is normal. Moreover `Spec(h) ≫ s g = s (h g)`.

Hence the sections of an étale sheaf `F` over `N_k` are the `G`-equivariant families of sections
of `F` over `Spec M` indexed by `G^{k + 1}`, and the Čech complex of `F` is the complex of
homogeneous cochains of `G` with values in `F(Spec M)`. For `F = 𝔾ₘ` the latter is the complex
computing `H^*(G, Mˣ)`, which vanishes in degree two when `K` is quasi-algebraically closed
(`IsQuasiAlgClosed.exists_eq_of_isCocycle`). This gives the vanishing of the second Čech
cohomology of `𝔾ₘ` for the covering, the input of the vanishing of `H²(Spec K_ét, 𝔾ₘ)`.

## Main statements

- `AlgebraicGeometry.Scheme.GaloisCech.iUnion_range_nerveSection`: the sections `s g` cover the
  Čech nerve.
- `AlgebraicGeometry.Scheme.GaloisCech.exactAt_two_cechComplex_gmSheaf`: the Čech complex of
  `𝔾ₘ` for the covering `Spec M ⟶ Spec K` is exact in degree two if `K` is `C₁`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Presheaf

namespace AlgebraicGeometry.Scheme

variable {K : Type u} [Field K]

/-- The terminal object `𝟙 : Spec K ⟶ Spec K` of the small étale site of `Spec K`. -/
local notation "𝟙ₑ" => MorphismProperty.Over.mk ⊤ (𝟙 (Spec (CommRingCat.of K)))
  (MorphismProperty.id_mem @AlgebraicGeometry.Etale (Spec (CommRingCat.of K)))

namespace GaloisCech

noncomputable def isTerminal : IsTerminal (𝟙ₑ : (Spec (.of K)).Etale) :=
  MorphismProperty.Over.mkIdTerminal _ _

variable (K) (M : Type u) [Field M] [Algebra K M] [Algebra.Etale K M]

/-- `Spec M`, as an object over the terminal object of the small étale site of `Spec K`. -/
noncomputable def cover : Over (𝟙ₑ : (Spec (.of K)).Etale) :=
  Over.mk (isTerminal.from (etaleSpec K M))

/-- The covering family consisting of `Spec M ⟶ Spec K`. -/
noncomputable def family : Fin 1 → Over (𝟙ₑ : (Spec (.of K)).Etale) := fun _ ↦ cover K M

variable {K M}

/-- The endomorphism `Spec σ` of `Spec M` over the terminal object. -/
noncomputable def coverMap (σ : M →ₐ[K] M) : cover K M ⟶ cover K M :=
  Over.homMk (etaleSpecMap σ) (isTerminal.hom_ext _ _)

lemma coverMap_comp (σ τ : M →ₐ[K] M) : coverMap σ ≫ coverMap τ = coverMap (σ.comp τ) := by
  ext1
  exact etaleSpecMap_comp τ σ

/-- The section `s g : Spec M ⟶ Spec M ×_K ⋯ ×_K Spec M` of the Čech nerve with components
`Spec (g l)`. -/
noncomputable def nerveSection {k : ℕ} (y : Fin (k + 1) → Fin 1) (g : Fin (k + 1) → Gal(M/K)) :
    cover K M ⟶ cechNerveObj (family K M) y :=
  Pi.lift fun l ↦ coverMap (g l).toAlgHom

@[reassoc (attr := simp)]
lemma nerveSection_π {k : ℕ} (y : Fin (k + 1) → Fin 1) (g : Fin (k + 1) → Gal(M/K))
    (l : Fin (k + 1)) :
    nerveSection y g ≫ Pi.π (fun l ↦ family K M (y l)) l = coverMap (g l).toAlgHom :=
  Pi.lift_comp_π _ _

lemma coverMap_nerveSection {k : ℕ} (y : Fin (k + 1) → Fin 1) (g : Fin (k + 1) → Gal(M/K))
    (h : Gal(M/K)) :
    coverMap h.toAlgHom ≫ nerveSection y g = nerveSection y (fun l ↦ h * g l) :=
  Pi.hom_ext _ _ fun l ↦ by
    rw [Category.assoc, nerveSection_π, nerveSection_π, coverMap_comp]
    rfl

lemma nerveSection_cechNerveMap {k m : ℕ} (y : Fin (m + 1) → Fin 1)
    (θ : Fin (k + 1) → Fin (m + 1)) (g : Fin (m + 1) → Gal(M/K)) :
    nerveSection y g ≫ cechNerveMap (family K M) y θ = nerveSection (y ∘ θ) (g ∘ θ) :=
  Pi.hom_ext _ _ fun l ↦ by
    rw [Category.assoc]
    erw [Pi.lift_comp_π, nerveSection_π, nerveSection_π]
    rfl

section Covering

/-- The ring map `A → Γ(X, 𝒪_X)` corresponding to a morphism `X ⟶ Spec A`. -/
noncomputable def toRing {X : Scheme.{u}} {A : CommRingCat.{u}} (h : X ⟶ Spec A) :
    A →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso A).inv ≫ h.appTop).hom

lemma toRing_comp_specMap {X : Scheme.{u}} {A B : CommRingCat.{u}} (h : X ⟶ Spec B)
    (φ : A ⟶ B) : toRing (h ≫ Spec.map φ) = (toRing h).comp φ.hom := by
  rw [toRing, toRing, Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality,
    Category.assoc]
  rfl

lemma eq_of_toRing_eq {X : Scheme.{u}} {A : CommRingCat.{u}} {h h' : X ⟶ Spec A}
    (e : toRing h = toRing h') : h = h' := by
  refine ext_of_isAffine ?_
  have : (Scheme.ΓSpecIso A).inv ≫ h.appTop = (Scheme.ΓSpecIso A).inv ≫ h'.appTop :=
    CommRingCat.hom_ext e
  rwa [cancel_epi] at this

variable [IsGalois K M]

/-- **The sections `s g` cover the Čech nerve.** A point of `Spec M ×_K ⋯ ×_K Spec M` with
residue field `E` is given by embeddings `ιₗ : M → E`, and `ιₗ = ι₀ ∘ gₗ` for some `gₗ ∈ G` since
`M / K` is normal; the point is then in the image of `s g`. -/
theorem iUnion_range_nerveSection {k : ℕ} (y : Fin (k + 1) → Fin 1) :
    ⋃ g : Fin (k + 1) → Gal(M/K), Set.range (nerveSection y g).left.left = Set.univ := by
  refine Set.eq_univ_of_forall fun z ↦ ?_
  let N := (cechNerveObj (family K M) y).left
  have := discreteTopology_of_etale_of_unique N
  let O : N.left.Opens := ⟨{z}, isOpen_discrete _⟩
  let W := Etale.ofOpens N O
  have : Subsingleton W.left := ⟨fun a b ↦ Subtype.ext (a.2.trans b.2.symm)⟩
  have : Nonempty W.left := ⟨⟨z, rfl⟩⟩
  let := (isField_of_etale_of_subsingleton W).toField
  let incl : Over.mk (isTerminal.from W) ⟶ cechNerveObj (family K M) y :=
    Over.homMk (Etale.ofOpensι N O) (isTerminal.hom_ext _ _)
  -- the embeddings `ιₗ: M → Γ(W, 𝒪)`
  let ι (l : Fin (k + 1)) : M →+* Γ(W.left, ⊤) :=
    toRing (incl ≫ Pi.π (fun l ↦ family K M (y l)) l).left.left
  let κ : K →+* Γ(W.left, ⊤) := toRing W.hom
  have hι (l : Fin (k + 1)) : (ι l).comp (algebraMap K M) = κ := by
    have h := MorphismProperty.Over.w (incl ≫ Pi.π (fun l ↦ family K M (y l)) l).left
    change _ ≫ Spec.map (CommRingCat.ofHom (algebraMap K M)) = W.hom at h
    simp only [ι, κ, ← h, toRing_comp_specMap]
    rfl
  let : Algebra K Γ(W.left, ⊤) := κ.toAlgebra
  let ιA (l : Fin (k + 1)) : M →ₐ[K] Γ(W.left, ⊤) :=
    { ι l with commutes' := fun c ↦ congrArg (fun φ : K →+* _ ↦ φ c) (hι l) }
  -- `ιₗ = ι₀ ∘ τₗ` with `τₗ ∈ G`, by normality
  let : Algebra M Γ(W.left, ⊤) := (ι 0).toAlgebra
  have : IsScalarTower K M Γ(W.left, ⊤) :=
    .of_algebraMap_eq fun c ↦ (congrArg (fun φ : K →+* _ ↦ φ c) (hι 0)).symm
  let τ (l : Fin (k + 1)) : Gal(M/K) := (ιA l).restrictNormal' M
  have hτ (l : Fin (k + 1)) (x : M) : ι 0 (τ l x) = ι l x :=
    (ιA l).restrictNormal_commutes M x
  have hincl : incl = (incl ≫ Pi.π (fun l ↦ family K M (y l)) 0) ≫ nerveSection y τ := by
    refine Pi.hom_ext _ _ fun l ↦ ?_
    rw [Category.assoc, nerveSection_π]
    ext1
    refine MorphismProperty.Over.Hom.ext (eq_of_toRing_eq ?_)
    change ι l = toRing (_ ≫ Spec.map (CommRingCat.ofHom (τ l).toAlgHom.toRingHom))
    rw [toRing_comp_specMap]
    ext x
    exact (hτ l x).symm
  refine Set.mem_iUnion.2
    ⟨τ, (Pi.π (fun l ↦ family K M (y l)) 0).left.left (incl.left.left ⟨z, rfl⟩), ?_⟩
  have := congrArg (fun φ ↦ φ.left.left ⟨z, rfl⟩) hincl
  simp only [Over.comp_left, MorphismProperty.Comma.comp_left, Scheme.Hom.comp_apply] at this
  exact this.symm.trans rfl

end Covering

section Sections

lemma etaleSpecMap_id : etaleSpecMap (AlgHom.id K M) = 𝟙 (etaleSpec K M) := by
  apply MorphismProperty.Over.Hom.ext
  change Spec.map (CommRingCat.ofHom (RingHom.id M)) = 𝟙 _
  exact Spec.map_id _

/-- Morphisms `b : Z ⟶ Spec M` from a nonempty scheme can be cancelled on the left of the maps
`Spec σ`. -/
lemma eq_of_comp_etaleSpecMap_eq {Z : (Spec (.of K)).Etale} [Nonempty Z.left]
    (b : Z ⟶ etaleSpec K M) {σ σ' : M →ₐ[K] M}
    (h : b ≫ etaleSpecMap σ = b ≫ etaleSpecMap σ') : σ = σ' := by
  have : Nonempty (⊤ : Z.left.Opens) := ⟨⟨Classical.arbitrary Z.left, trivial⟩⟩
  have h' := congrArg (fun φ ↦ toRing φ.left) h
  change toRing (b.left ≫ Spec.map _) = toRing (b.left ≫ Spec.map _) at h'
  rw [toRing_comp_specMap, toRing_comp_specMap] at h'
  ext x
  exact (toRing b.left).injective (congrArg (fun φ : M →+* _ ↦ φ x) h')

/-- The value `c(s g) ∈ Mˣ` of a section `c` of `𝔾ₘ` over the Čech nerve at the section `s g`. -/
noncomputable def evalSection {k : ℕ} (y : Fin (k + 1) → Fin 1) (g : Fin (k + 1) → Gal(M/K)) :
    (Spec (.of K)).gmSheaf.obj.obj (op (cechNerveObj (family K M) y).left) →+ Additive Mˣ :=
  (gmSheafEtaleSpecEquiv M).toAddMonoidHom.comp
    ((Spec (.of K)).gmSheaf.obj.map (nerveSection y g).left.op).hom

lemma evalSection_smul {k : ℕ} (y : Fin (k + 1) → Fin 1) (g : Fin (k + 1) → Gal(M/K))
    (h : Gal(M/K)) (c : (Spec (.of K)).gmSheaf.obj.obj (op (cechNerveObj (family K M) y).left)) :
    evalSection y (fun l ↦ h * g l) c =
      .ofMul (Units.map h.toAlgHom.toMonoidHom (evalSection y g c).toMul) := by
  simp only [evalSection, AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom,
    Function.comp_apply, ← coverMap_nerveSection, Over.comp_left, op_comp,
    Functor.map_comp]
  exact gmSheafEtaleSpecEquiv_map h.toAlgHom _

lemma evalSection_map {k m : ℕ} (y : Fin (m + 1) → Fin 1) (θ : Fin (k + 1) → Fin (m + 1))
    (g : Fin (m + 1) → Gal(M/K))
    (c : (Spec (.of K)).gmSheaf.obj.obj (op (cechNerveObj (family K M) (y ∘ θ)).left)) :
    evalSection y g ((Spec (.of K)).gmSheaf.obj.map (cechNerveMap (family K M) y θ).left.op c) =
      evalSection (y ∘ θ) (g ∘ θ) c := by
  change gmSheafEtaleSpecEquiv M ((Spec (.of K)).gmSheaf.obj.map (nerveSection y g).left.op
    ((Spec (.of K)).gmSheaf.obj.map (cechNerveMap (family K M) y θ).left.op c)) =
    gmSheafEtaleSpecEquiv M
      ((Spec (.of K)).gmSheaf.obj.map (nerveSection (y ∘ θ) (g ∘ θ)).left.op c)
  rw [← nerveSection_cechNerveMap, Over.comp_left, op_comp, Functor.map_comp,
    ConcreteCategory.comp_apply]

variable [IsGalois K M]

/-- Sections of `𝔾ₘ` over the Čech nerve are determined by their values at the sections
`s g`. -/
lemma eq_of_evalSection_eq {k : ℕ} (y : Fin (k + 1) → Fin 1)
    {c c' : (Spec (.of K)).gmSheaf.obj.obj (op (cechNerveObj (family K M) y).left)}
    (h : ∀ g, evalSection y g c = evalSection y g c') : c = c' := by
  refine (isSheafFor_ofArrows (Spec (.of K)).gmSheaf (fun g ↦ (nerveSection y g).left)
    (iUnion_range_nerveSection y)).isSeparatedFor.ext fun Z f ⟨g⟩ ↦ ?_
  exact (gmSheafEtaleSpecEquiv M).injective (h g)

/-- **Gluing equivariant families.** A family `φ g ∈ Mˣ`, indexed by `g : G^{k + 1}`, with
`φ (h g) = h (φ g)` is the family of values at the sections `s g` of a section of `𝔾ₘ` over
the Čech nerve. -/
lemma exists_evalSection_eq {k : ℕ} (y : Fin (k + 1) → Fin 1)
    (φ : (Fin (k + 1) → Gal(M/K)) → Mˣ)
    (hφ : ∀ g h, φ (fun l ↦ h * g l) = Units.map h.toAlgHom.toMonoidHom (φ g)) :
    ∃ c, ∀ g, evalSection y g c = .ofMul (φ g) := by
  let e (g : Fin (k + 1) → Gal(M/K)) : (Spec (.of K)).gmSheaf.obj.obj (op (etaleSpec K M)) :=
    (gmSheafEtaleSpecEquiv M).symm (.ofMul (φ g))
  have he (g : Fin (k + 1) → Gal(M/K)) (h : Gal(M/K)) :
      (Spec (.of K)).gmSheaf.obj.map (etaleSpecMap h.toAlgHom).op (e g) = e (fun l ↦ h * g l) := by
    apply (gmSheafEtaleSpecEquiv M).injective
    rw [gmSheafEtaleSpecEquiv_map]
    simp only [e, AddEquiv.apply_symm_apply, toMul_ofMul]
    rw [hφ]
  obtain ⟨c, hc, -⟩ := (Presieve.isSheafFor_arrows_iff _ _).1
    (isSheafFor_ofArrows (Spec (.of K)).gmSheaf (fun g ↦ (nerveSection y g).left)
      (iUnion_range_nerveSection y)) e fun a b Z ga gb hab ↦ by
      by_cases hZ : IsEmpty Z.left
      · exact (subsingleton_obj_of_isEmpty (Spec (.of K)).gmSheaf (Z := Z)).elim _ _
      have : Nonempty Z.left := not_isEmpty_iff.1 hZ
      -- the components of `s a` and `s b`
      have hl (l : Fin (k + 1)) :
          ga ≫ etaleSpecMap (a l).toAlgHom = gb ≫ etaleSpecMap (b l).toAlgHom := by
        have := congrArg (fun φ ↦ φ ≫ (Pi.π (fun l ↦ family K M (y l)) l).left) hab
        simp only [Category.assoc, ← Over.comp_left, nerveSection_π] at this
        exact this
      set σ := b 0 * (a 0)⁻¹ with hσ
      have hga : ga = gb ≫ etaleSpecMap σ.toAlgHom := by
        have hid : (a 0).toAlgHom.comp (a 0)⁻¹.toAlgHom = AlgHom.id K M := by
          ext x
          simp
        calc ga = ga ≫ etaleSpecMap ((a 0).toAlgHom.comp (a 0)⁻¹.toAlgHom) := by
              rw [hid, etaleSpecMap_id]
              exact (Category.comp_id ga).symm
          _ = gb ≫ etaleSpecMap (b 0).toAlgHom ≫ etaleSpecMap (a 0)⁻¹.toAlgHom := by
              rw [← etaleSpecMap_comp, ← Category.assoc, hl 0, Category.assoc]
          _ = gb ≫ etaleSpecMap σ.toAlgHom := by
              rw [etaleSpecMap_comp]
              rfl
      have hb : b = fun l ↦ σ * a l := by
        funext l
        have := hl l
        rw [hga, Category.assoc, etaleSpecMap_comp] at this
        have h2 := eq_of_comp_etaleSpecMap_eq gb this
        exact (AlgEquiv.ext fun x ↦ DFunLike.congr_fun h2 x).symm
      change (Spec (.of K)).gmSheaf.obj.map ga.op (e a) = (Spec (.of K)).gmSheaf.obj.map gb.op (e b)
      rw [hb, hga, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
      exact congrArg ((Spec (.of K)).gmSheaf.obj.map gb.op) (he a σ)
  refine ⟨c, fun g ↦ ?_⟩
  have := hc g
  change (Spec (.of K)).gmSheaf.obj.map (nerveSection y g).left.op c = e g at this
  change gmSheafEtaleSpecEquiv M ((Spec (.of K)).gmSheaf.obj.map (nerveSection y g).left.op c) = _
  rw [this]
  exact AddEquiv.apply_symm_apply _ _

end Sections

section Exactness

lemma vec_three {α : Type*} (g : Fin 3 → α) : g = ![g 0, g 1, g 2] := by
  funext l
  fin_cases l <;> rfl

variable [FiniteDimensional K M] [IsGalois K M]

/-- **The second Čech cohomology of `𝔾ₘ` for a Galois covering of a `C₁` field vanishes.** The
Čech complex of `𝔾ₘ` for the covering `Spec M ⟶ Spec K` is the complex of homogeneous
cochains of `Gal(M/K)` with values in `Mˣ` (`AlgebraicGeometry.Scheme.GaloisCech.evalSection`),
whose cohomology in degree two vanishes by
`IsQuasiAlgClosed.exists_eq_of_isHomogeneousCocycle`. -/
theorem exactAt_two_cechComplex_gmSheaf [IsQuasiAlgClosed K] :
    ((cechComplex (family K M)).obj (Spec (.of K)).gmSheaf.obj).ExactAt 2 := by
  refine (exactAt_cechComplex_iff (family K M) _ 1).2 fun c hc ↦ ?_
  -- the homogeneous cochain `F` attached to `c`
  let F : Gal(M/K) → Gal(M/K) → Gal(M/K) → Mˣ := fun a b d ↦
    (evalSection (fun _ ↦ 0) ![a, b, d] (c fun _ ↦ 0)).toMul
  have hF (h a b d : Gal(M/K)) :
      F (h * a) (h * b) (h * d) = Units.map h.toAlgHom.toMonoidHom (F a b d) := by
    have := evalSection_smul (fun _ ↦ (0 : Fin 1)) ![a, b, d] h (c fun _ ↦ 0)
    have e : (fun l ↦ h * ![a, b, d] l) = ![h * a, h * b, h * d] := by
      funext l
      fin_cases l <;> rfl
    rw [e] at this
    exact congrArg Additive.toMul this
  have hcoc (a b d e : Gal(M/K)) : F b d e * (F a d e)⁻¹ * F a b e * (F a b d)⁻¹ = 1 := by
    have := congrArg (evalSection (fun _ ↦ (0 : Fin 1)) ![a, b, d, e]) (congrFun hc fun _ ↦ 0)
    rw [cechComplex_d_apply, map_sum, Fin.sum_univ_four] at this
    simp only [map_zsmul, evalSection_map] at this
    have e0 : ![a, b, d, e] ∘ (0 : Fin 4).succAbove = ![b, d, e] := by
      funext l; fin_cases l <;> rfl
    have e1 : ![a, b, d, e] ∘ (1 : Fin 4).succAbove = ![a, d, e] := by
      funext l; fin_cases l <;> rfl
    have e2 : ![a, b, d, e] ∘ (2 : Fin 4).succAbove = ![a, b, e] := by
      funext l; fin_cases l <;> rfl
    have e3 : ![a, b, d, e] ∘ (3 : Fin 4).succAbove = ![a, b, d] := by
      funext l; fin_cases l <;> rfl
    rw [e0, e1, e2, e3, cechComplex_zero_apply, map_zero] at this
    change (-1 : ℤ) ^ ((0 : Fin 4) : ℕ) • Additive.ofMul (F b d e) +
      (-1 : ℤ) ^ ((1 : Fin 4) : ℕ) • Additive.ofMul (F a d e) +
      (-1 : ℤ) ^ ((2 : Fin 4) : ℕ) • Additive.ofMul (F a b e) +
      (-1 : ℤ) ^ ((3 : Fin 4) : ℕ) • Additive.ofMul (F a b d) = 0 at this
    have := congrArg Additive.toMul this
    simpa [div_eq_mul_inv, mul_assoc] using this
  obtain ⟨E, hE, hFE⟩ := IsQuasiAlgClosed.exists_eq_of_isHomogeneousCocycle F hF hcoc
  -- `E` glues to a cochain `b`
  obtain ⟨b, hb⟩ := exists_evalSection_eq (fun _ : Fin 2 ↦ (0 : Fin 1))
    (fun g ↦ E (g 0) (g 1)) fun g h ↦ hE h (g 0) (g 1)
  refine ⟨fun y ↦ (Subsingleton.elim (fun _ ↦ (0 : Fin 1)) y) ▸ b, ?_⟩
  funext y
  obtain rfl : y = fun _ ↦ 0 := Subsingleton.elim _ _
  refine eq_of_evalSection_eq _ fun g ↦ ?_
  rw [cechComplex_d_apply, map_sum, Fin.sum_univ_three]
  simp only [map_zsmul, evalSection_map]
  have h0 : evalSection (fun _ ↦ (0 : Fin 1)) (g ∘ (0 : Fin 3).succAbove) b =
      .ofMul (E (g 1) (g 2)) := hb _
  have h1 : evalSection (fun _ ↦ (0 : Fin 1)) (g ∘ (1 : Fin 3).succAbove) b =
      .ofMul (E (g 0) (g 2)) := hb _
  have h2 : evalSection (fun _ ↦ (0 : Fin 1)) (g ∘ (2 : Fin 3).succAbove) b =
      .ofMul (E (g 0) (g 1)) := hb _
  change (-1 : ℤ) ^ ((0 : Fin 3) : ℕ) • evalSection (fun _ ↦ (0 : Fin 1)) (g ∘ Fin.succAbove 0) b +
    (-1 : ℤ) ^ ((1 : Fin 3) : ℕ) • evalSection (fun _ ↦ (0 : Fin 1)) (g ∘ Fin.succAbove 1) b +
    (-1 : ℤ) ^ ((2 : Fin 3) : ℕ) • evalSection (fun _ ↦ (0 : Fin 1)) (g ∘ Fin.succAbove 2) b = _
  rw [h0, h1, h2]
  conv_rhs => rw [vec_three g]
  change _ = Additive.ofMul (F (g 0) (g 1) (g 2))
  rw [hFE]
  apply Additive.toMul.injective
  simp [mul_assoc]

end Exactness

end GaloisCech

end AlgebraicGeometry.Scheme
