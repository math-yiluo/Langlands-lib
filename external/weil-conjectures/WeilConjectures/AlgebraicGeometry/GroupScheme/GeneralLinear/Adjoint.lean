/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Kernel
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.RelativeFree

/-!
# The adjoint representation

Let `G` be a group scheme locally of finite type over a field `k` and `(b_i)_{i ∈ I}` a basis of
`Lie(G)`. For a scheme `X` over `k`, the infinitesimal points of `G` with values in `X` form the
free `Γ(X, 𝒪_X)`-module `Lie(G) ⊗ Γ(X, 𝒪_X)` with basis the base changes `(b_i)_X`
(`AlgebraicGeometry.GrpObj.existsUnique_prod_eq`), and an `X`-point `x` of `G` acts on it by
conjugation `v ↦ x v x⁻¹`. Its matrix in the basis `(b_i)_X` is an invertible matrix over
`Γ(X, 𝒪_X)`, functorial in `X` and multiplicative in `x`. Since `GL_I` is affine, its `X`-points
are the invertible matrices over `Γ(X, 𝒪_X)` (`AlgebraicGeometry.GeneralLinearGroup.homGLEquiv`),
so these matrices come from a single homomorphism of group schemes
`Ad : G ⟶ GL_I`, the *adjoint representation* (`AlgebraicGeometry.GrpObj.adjoint`): its value at
the universal point `𝟙 G`.

## Main definitions

- `AlgebraicGeometry.GeneralLinearGroup.homGLEquiv`: the `X`-points of `GL_n` are the group
  `GL n Γ(X, 𝒪_X)`, for every scheme `X` over `k`.
- `AlgebraicGeometry.GrpObj.adjointMatrix`: the matrix of the conjugation by an `X`-point on the
  infinitesimal points with values in `X`.
- `AlgebraicGeometry.GrpObj.adjoint`: the adjoint representation `Ad : G ⟶ GL(Lie G)`.

## Main statements

- `AlgebraicGeometry.GrpObj.homGLEquiv_comp_adjoint`: `Ad(x)` is the matrix of `v ↦ x v x⁻¹`.
- `AlgebraicGeometry.GrpObj.isMonHom_adjoint`: `Ad` is a homomorphism of group schemes.

## Blueprint

- `lemma-stable-subspaces-center`: the adjoint representation `Ad : G → GL(Lie G)`.
-/

@[expose] public section

universe u

open CategoryTheory TrivSqZeroExt
open scoped MonObj
open Matrix.GeneralLinearGroup (CoordinateRing)

namespace AlgebraicGeometry

/-! ### Points of `GL_n` with values in a scheme -/

namespace GeneralLinearGroup

variable {k : Type u} [Field k] (n : Type u) [Fintype n] [DecidableEq n]

/-- The entries of the matrix of a point `p : Spec R ⟶ GL_n` over `k`, read in `Γ(Spec R, 𝒪)`,
are the pullbacks along `p` of the coordinate functions `x_ij` of `GL_n`. -/
theorem ΓSpecIso_inv_homMulEquiv_apply {R : Type u} [CommRing R] [Algebra k R]
    (p : (Spec (.of R)).asOver (Spec (.of k)) ⟶ 𝔾𝕃(n; k)) (i j : n) :
    (Scheme.ΓSpecIso (.of R)).inv (homMulEquiv n k R p i j) =
      p.left.appTop ((Scheme.ΓSpecIso (.of (CoordinateRing n k))).inv
        (Matrix.GeneralLinearGroup.coord n k i j)) := by
  have h1 := RationalHom.points_apply_apply (G := 𝔾𝕃(n; k)) (𝟙 _) p i j
  have h2 := RationalHom.appTop_appTop_ΓSpecIso_inv (G := 𝔾𝕃(n; k)) (𝟙 _) p
    (Matrix.GeneralLinearGroup.coord n k i j)
  rw [RationalHom.points_apply, Category.comp_id] at h1
  rw [Category.comp_id] at h2
  rw [h1, ← h2]
  simp

section HomGLEquiv

variable (X : Over (Spec (.of k)))

/-- The `k`-algebra structure on `Γ(X, 𝒪_X)` of a scheme `X` over `k`. -/
noncomputable abbrev overΓAlgebra : Algebra k Γ(X.left, ⊤) :=
  (GrpObj.overΓAlgebraMap X).toAlgebra

attribute [local instance] overΓAlgebra

/-- The canonical morphism `X ⟶ Spec Γ(X, 𝒪_X)`, over `k`. -/
noncomputable def toSpecΓOver : X ⟶ (Spec (.of Γ(X.left, ⊤))).asOver (Spec (.of k)) :=
  Over.homMk X.left.toSpecΓ (Scheme.toSpecΓ_SpecMap_ΓSpecIso_inv_appTop X.hom)

variable {X} in
/-- A morphism over `k` from `X` to an affine scheme `Spec B` over `k` is determined by its
`k`-algebra homomorphism `B → Γ(X, 𝒪_X)`: it factors uniquely through `X ⟶ Spec Γ(X, 𝒪_X)`. -/
theorem bijective_toSpecΓOver_comp {B : Type u} [CommRing B] [Algebra k B] :
    Function.Bijective fun q : (Spec (.of Γ(X.left, ⊤))).asOver (Spec (.of k)) ⟶
        (Spec (.of B)).asOver (Spec (.of k)) ↦ toSpecΓOver X ≫ q := by
  refine ⟨fun q₁ q₂ h ↦ ?_, fun p ↦ ?_⟩
  · have h' : X.left.toSpecΓ ≫ q₁.left = X.left.toSpecΓ ≫ q₂.left := congrArg Over.Hom.left h
    have e₁ := Scheme.ΓSpecIso_inv_comp_toSpecΓ_specMap_appTop (Y := X.left)
      (Spec.preimage q₁.left)
    have e₂ := Scheme.ΓSpecIso_inv_comp_toSpecΓ_specMap_appTop (Y := X.left)
      (Spec.preimage q₂.left)
    rw [Spec.map_preimage] at e₁ e₂
    rw [h'] at e₁
    exact Over.OverMorphism.ext (by rw [← Spec.map_preimage q₁.left, ← e₁, e₂, Spec.map_preimage])
  · set φ := (Scheme.ΓSpecIso (.of B)).inv ≫ p.left.appTop
    have hφ : CommRingCat.ofHom (algebraMap k B) ≫ φ =
        CommRingCat.ofHom (algebraMap k Γ(X.left, ⊤)) := by
      have h := congrArg (fun f ↦ (Scheme.ΓSpecIso (.of k)).inv ≫ Scheme.Hom.appTop f) (Over.w p)
      simp only [OverClass.asOver_hom, specOverSpec_over, Scheme.Hom.comp_appTop] at h
      rw [← Category.assoc, Scheme.ΓSpecIso_inv_comp_specMap_appTop, Category.assoc] at h
      exact h
    refine ⟨Over.homMk (Spec.map φ) ?_, Over.OverMorphism.ext ?_⟩
    · simp only [OverClass.asOver_hom, specOverSpec_over]
      rw [← Spec.map_comp, hφ]
    · exact Scheme.toSpecΓ_SpecMap_ΓSpecIso_inv_appTop p.left

/-- **The points of `GL_n` with values in a scheme.** For a scheme `X` over `k`, the morphisms
`X ⟶ GL_n` over `k` are the invertible `n × n` matrices over `Γ(X, 𝒪_X)`, as groups: such a
morphism factors uniquely through `X ⟶ Spec Γ(X, 𝒪_X)`. (blueprint: `det-d-geometry`) -/
noncomputable def homGLEquiv : (X ⟶ 𝔾𝕃(n; k)) ≃* GL n Γ(X.left, ⊤) :=
  (MulEquiv.ofBijective (pointsPrecomp 𝔾𝕃(n; k) (toSpecΓOver X))
    bijective_toSpecΓOver_comp).symm.trans (homMulEquiv n k Γ(X.left, ⊤))

theorem homGLEquiv_toSpecΓOver_comp
    (q : (Spec (.of Γ(X.left, ⊤))).asOver (Spec (.of k)) ⟶ 𝔾𝕃(n; k)) :
    homGLEquiv n X (toSpecΓOver X ≫ q) = homMulEquiv n k Γ(X.left, ⊤) q := by
  rw [homGLEquiv, MulEquiv.trans_apply]
  congr 1
  rw [MulEquiv.symm_apply_eq]
  rfl

variable {X} in
/-- The `k`-algebra homomorphism `Γ(X, 𝒪_X) → Γ(Y, 𝒪_Y)` of a morphism `φ : Y ⟶ X` over `k`. -/
noncomputable def appTopAlgHom {Y : Over (Spec (.of k))} (φ : Y ⟶ X) :
    Γ(X.left, ⊤) →ₐ[k] Γ(Y.left, ⊤) :=
  { φ.left.appTop.hom with commutes' c := GrpObj.appTop_overΓAlgebraMap φ c }

theorem comp_toSpecΓOver {Y : Over (Spec (.of k))} (φ : Y ⟶ X) :
    φ ≫ toSpecΓOver X = toSpecΓOver Y ≫
      (Spec.map (CommRingCat.ofHom (appTopAlgHom φ).toRingHom)).asOver (Spec (.of k)) := by
  ext1
  exact Scheme.toSpecΓ_naturality φ.left

/-- The identification `homGLEquiv` is natural in `X`: precomposing with `φ : Y ⟶ X` maps the
entries along `Γ(X, 𝒪_X) → Γ(Y, 𝒪_Y)`. -/
theorem homGLEquiv_comp {Y : Over (Spec (.of k))} (φ : Y ⟶ X) (p : X ⟶ 𝔾𝕃(n; k)) :
    homGLEquiv n Y (φ ≫ p) =
      Matrix.GeneralLinearGroup.map φ.left.appTop.hom (homGLEquiv n X p) := by
  obtain ⟨q, rfl⟩ := (bijective_toSpecΓOver_comp (X := X)).2 p
  rw [← Category.assoc, comp_toSpecΓOver, Category.assoc, homGLEquiv_toSpecΓOver_comp,
    homGLEquiv_toSpecΓOver_comp, homMulEquiv_specMap_comp]
  rfl

theorem homGLEquiv_injective : Function.Injective (homGLEquiv n X) :=
  (homGLEquiv n X).injective

/-- The entries of the matrix of a point `p : X ⟶ GL_n` are the pullbacks along `p` of the
coordinate functions `x_ij` of `GL_n`. -/
theorem homGLEquiv_apply_apply (p : X ⟶ 𝔾𝕃(n; k)) (i j : n) :
    homGLEquiv n X p i j = p.left.appTop ((Scheme.ΓSpecIso (.of (CoordinateRing n k))).inv
      (Matrix.GeneralLinearGroup.coord n k i j)) := by
  obtain ⟨q, rfl⟩ := (bijective_toSpecΓOver_comp (X := X)).2 p
  rw [homGLEquiv_toSpecΓOver_comp, Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    ← ΓSpecIso_inv_homMulEquiv_apply n q i j]
  change _ = X.left.toSpecΓ.appTop _
  rw [Scheme.toSpecΓ_appTop]
  exact (Iso.inv_hom_id_apply (Scheme.ΓSpecIso Γ(X.left, ⊤)) _).symm

/-- For an affine scheme `Spec R` over `k`, `homGLEquiv` is `homMulEquiv` read in
`Γ(Spec R, 𝒪) ≅ R`. -/
theorem homGLEquiv_asOver_apply {R : Type u} [CommRing R] [Algebra k R]
    (p : (Spec (.of R)).asOver (Spec (.of k)) ⟶ 𝔾𝕃(n; k)) (i j : n) :
    homGLEquiv n _ p i j = (Scheme.ΓSpecIso (.of R)).inv (homMulEquiv n k R p i j) :=
  (homGLEquiv_apply_apply n _ p i j).trans (ΓSpecIso_inv_homMulEquiv_apply n p i j).symm

end HomGLEquiv

end GeneralLinearGroup

/-! ### The adjoint representation -/

namespace GrpObj

open GeneralLinearGroup MonoidalCategory CartesianMonoidalCategory

variable {k : Type u} [Field k] {G : Over (Spec (.of k))} [GrpObj G] [LocallyOfFiniteType G.hom]
  {I : Type u} [Fintype I] (b : Module.Basis I k (Lie G))

/-- The matrix of the conjugation `v ↦ x v x⁻¹` by an `X`-point `x` of `G` on the infinitesimal
points of `G` with values in `X`, in the basis `(b_i)_X`: the `j`-th column holds the coordinates
of `x (b_j)_X x⁻¹`. (blueprint: `lemma-stable-subspaces-center`) -/
noncomputable def adjointMatrix {X : Over (Spec (.of k))} (x : X ⟶ G) : Matrix I I Γ(X.left, ⊤) :=
  Matrix.of fun i j ↦ infPointsAtCoord b X (infPointsAtConj x (lieAt X (b j))) i

theorem adjointMatrix_apply {X : Over (Spec (.of k))} (x : X ⟶ G) (i j : I) :
    adjointMatrix b x i j = infPointsAtCoord b X (infPointsAtConj x (lieAt X (b j))) i :=
  rfl

open scoped IsMulCommutative in
/-- The conjugation by `x` acts on coordinates by the matrix `adjointMatrix b x`. -/
theorem infPointsAtCoord_infPointsAtConj {X : Over (Spec (.of k))} (x : X ⟶ G)
    (v : infPointsAt G X) :
    infPointsAtCoord b X (infPointsAtConj x v) =
      (adjointMatrix b x).mulVec (infPointsAtCoord b X v) := by
  conv_lhs => rw [← prod_infPointsAtCoord b X v]
  rw [map_prod, infPointsAtCoord_prod]
  ext i
  simp only [infPointsAtConj_infPointsAtScale, infPointsAtCoord_infPointsAtScale,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, adjointMatrix_apply]
  exact Finset.sum_congr rfl fun l _ ↦ mul_comm _ _

theorem adjointMatrix_mul {X : Over (Spec (.of k))} (x y : X ⟶ G) :
    adjointMatrix b (x * y) = adjointMatrix b x * adjointMatrix b y := by
  ext i j
  rw [adjointMatrix_apply, infPointsAtConj_mul, infPointsAtCoord_infPointsAtConj, Matrix.mul_apply]
  simp only [Matrix.mulVec, dotProduct, adjointMatrix_apply]

/-- The matrices of the conjugations are natural in `X`. -/
theorem adjointMatrix_comp {X Y : Over (Spec (.of k))} (φ : Y ⟶ X) (x : X ⟶ G) :
    adjointMatrix b (φ ≫ x) = (adjointMatrix b x).map φ.left.appTop := by
  ext i j
  rw [adjointMatrix_apply, ← infPointsAtMap_lieAt X φ, ← infPointsAtMap_infPointsAtConj,
    infPointsAtCoord_infPointsAtMap, Matrix.map_apply, adjointMatrix_apply]

variable [DecidableEq I]

theorem adjointMatrix_one (X : Over (Spec (.of k))) : adjointMatrix b (1 : X ⟶ G) = 1 := by
  ext i j
  simp only [adjointMatrix_apply, infPointsAtConj_one, infPointsAtCoord_lieAt,
    Module.Basis.repr_self, Matrix.one_apply, Finsupp.single_apply]
  split_ifs with h₁ h₂ h₂
  · exact map_one _
  · exact absurd h₁.symm h₂
  · exact absurd h₂.symm h₁
  · exact map_zero _

/-- The adjoint action of the `X`-points of `G` on `Lie(G) ⊗ Γ(X, 𝒪_X)`, as a group homomorphism
`G(X) → GL_I(Γ(X, 𝒪_X))`. -/
noncomputable def adjointHom (X : Over (Spec (.of k))) : (X ⟶ G) →* GL I Γ(X.left, ⊤) :=
  MonoidHom.toHomUnits
    { toFun := adjointMatrix b
      map_one' := adjointMatrix_one b X
      map_mul' := adjointMatrix_mul b }

@[simp]
theorem coe_adjointHom {X : Over (Spec (.of k))} (x : X ⟶ G) :
    (adjointHom b X x : Matrix I I Γ(X.left, ⊤)) = adjointMatrix b x :=
  rfl

theorem adjointHom_comp {X Y : Over (Spec (.of k))} (φ : Y ⟶ X) (x : X ⟶ G) :
    adjointHom b Y (φ ≫ x) = Matrix.GeneralLinearGroup.map φ.left.appTop.hom (adjointHom b X x) :=
  Units.ext (adjointMatrix_comp b φ x)

/-- **The adjoint representation** `Ad : G ⟶ GL(Lie G)` of a group scheme `G` locally of finite
type over a field `k`, in a basis `(b_i)` of `Lie(G)`: the morphism to `GL_I` whose value at an
`X`-point `x` of `G` is the matrix of the conjugation `v ↦ x v x⁻¹` on `Lie(G) ⊗ Γ(X, 𝒪_X)`
(`homGLEquiv_comp_adjoint`). It is the value of these matrices at the universal point `𝟙 G`.
(blueprint: `lemma-stable-subspaces-center`) -/
noncomputable def adjoint : G ⟶ 𝔾𝕃(I; k) :=
  (homGLEquiv I G).symm (adjointHom b G (𝟙 G))

/-- The matrix of `Ad` at an `X`-point `x` of `G` is the matrix of the conjugation by `x` on the
infinitesimal points with values in `X`. (blueprint: `lemma-stable-subspaces-center`) -/
theorem homGLEquiv_comp_adjoint {X : Over (Spec (.of k))} (x : X ⟶ G) :
    homGLEquiv I X (x ≫ adjoint b) = adjointHom b X x := by
  rw [homGLEquiv_comp, adjoint, MulEquiv.apply_symm_apply, ← adjointHom_comp, Category.comp_id]

/-- The adjoint representation is a homomorphism of group schemes. -/
instance isMonHom_adjoint : IsMonHom (adjoint b) where
  one_hom := by
    have h1 (H : Over (Spec (.of k))) [GrpObj H] : (η[H] : 𝟙_ _ ⟶ H) = 1 := by
      rw [Hom.one_def, toUnit_unit, Category.id_comp]
    apply homGLEquiv_injective I (𝟙_ (Over (Spec (.of k))))
    rw [homGLEquiv_comp_adjoint, h1, h1, map_one, map_one]
  mul_hom := by
    have hμ (H : Over (Spec (.of k))) [GrpObj H] : μ[H] = fst H H * snd H H := by
      rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
    apply homGLEquiv_injective I (G ⊗ G)
    rw [homGLEquiv_comp_adjoint, hμ G, map_mul, ← homGLEquiv_comp_adjoint,
      ← homGLEquiv_comp_adjoint, ← map_mul, Hom.mul_def, lift_fst_comp_snd_comp]

/-! ### The adjoint representation at rational points -/

theorem overΓAlgebraMap_unit (c : k) :
    overΓAlgebraMap (𝟙_ (Over (Spec (.of k)))) c = (Scheme.ΓSpecIso (.of k)).inv c := by
  simp [overΓAlgebraMap]

omit [LocallyOfFiniteType G.hom] in
/-- At a rational point `g`, the conjugation of the infinitesimal points with values in `Spec k`
is the differential of the conjugation `c_g` of `G`. -/
theorem infPointsAtConj_lieAt_unit (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) (y : Lie G) :
    infPointsAtConj g (lieAt (𝟙_ (Over (Spec (.of k)))) y) =
      lieAt (𝟙_ (Over (Spec (.of k)))) (differential (conjBy G g) y) := by
  have hp : overDualNumbersProj (𝟙_ (Over (Spec (.of k)))) = toUnit _ := toUnit_unique _ _
  apply Subtype.ext
  rw [coe_infPointsAtConj, coe_lieAt, coe_lieAt, tangentPoint_differential, ← Category.assoc,
    comp_conjBy, hp, GrpObj.comp_inv]

/-- At a rational point `g`, the matrix of the conjugation is the matrix of `Ad(g) = d(c_g)`. -/
theorem adjointMatrix_unit (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    adjointMatrix b g = (LinearMap.toMatrix b b
      (differential (conjBy G g) : Lie G →ₗ[k] Lie G)).map (Scheme.ΓSpecIso (.of k)).inv := by
  ext i j
  rw [adjointMatrix_apply, infPointsAtConj_lieAt_unit, infPointsAtCoord_lieAt, Matrix.map_apply,
    LinearMap.toMatrix_apply]
  exact overΓAlgebraMap_unit _

/-- **The adjoint representation at a rational point.** For a rational point `g` of `G`, `Ad(g)`
is the matrix in the basis `(b_i)` of the differential `d(c_g)` of the conjugation by `g`, read
in `Γ(Spec k, 𝒪) ≅ k`. (blueprint: `lemma-stable-subspaces-center`) -/
theorem homGLEquiv_comp_adjoint_unit (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    ((homGLEquiv I _ (g ≫ adjoint b) : GL I _) :
      Matrix I I Γ((𝟙_ (Over (Spec (.of k)))).left, ⊤)) =
      (LinearMap.toMatrix b b
        (differential (conjBy G g) : Lie G →ₗ[k] Lie G)).map (Scheme.ΓSpecIso (.of k)).inv := by
  rw [homGLEquiv_comp_adjoint, coe_adjointHom, adjointMatrix_unit]

/-- **The Lie algebra of a centralizer is the fixed space of `Ad(g)`.** A tangent vector `x` is
tangent to the centralizer `C_G(g)` of a rational point `g` if and only if `Ad(g)` fixes its
coordinates in the basis `(b_i)`. (blueprint: `lemma-stable-subspaces-center`) -/
theorem mem_range_differential_centralizerι_iff_adjoint (g : 𝟙_ (Over (Spec (.of k))) ⟶ G)
    (x : Lie G) :
    x ∈ (differential (centralizerι g)).range ↔
      ((homGLEquiv I _ (g ≫ adjoint b) : GL I _) :
      Matrix I I Γ((𝟙_ (Over (Spec (.of k)))).left, ⊤)).mulVec
          ((Scheme.ΓSpecIso (.of k)).inv ∘ b.repr x) =
        (Scheme.ΓSpecIso (.of k)).inv ∘ b.repr x := by
  have hσ : Function.Injective (Scheme.ΓSpecIso (.of k)).inv :=
    ((Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv).injective
  rw [mem_range_differential_centralizerι_iff, homGLEquiv_comp_adjoint_unit]
  have h : ((LinearMap.toMatrix b b (differential (conjBy G g) : Lie G →ₗ[k] Lie G)).map
      (Scheme.ΓSpecIso (.of k)).inv.hom).mulVec ((Scheme.ΓSpecIso (.of k)).inv ∘ b.repr x) =
      (Scheme.ΓSpecIso (.of k)).inv ∘ b.repr (differential (conjBy G g) x) := by
    ext i
    rw [← RingHom.map_mulVec, LinearMap.toMatrix_mulVec_repr]
    rfl
  rw [h]
  refine ⟨fun e ↦ by rw [e], fun e ↦ b.repr.injective (Finsupp.ext fun i ↦ hσ ?_)⟩
  exact congrFun e i

/-! ### The differential of the adjoint representation -/

section DifferentialAdjoint

/-- The thickening `(Spec R)[ε] ⟶ Spec R[ε]` is natural in the ring `R`. -/
theorem _root_.AlgebraicGeometry.Scheme.dualNumbersToSpec_naturality {R S : CommRingCat.{u}}
    (f : R ⟶ S) :
    (Spec.map f).dualNumbers ≫ Scheme.dualNumbersToSpec R =
      Scheme.dualNumbersToSpec S ≫ Spec.map (CommRingCat.ofHom (DualNumber.mapRingHom f.hom)) := by
  have h := Scheme.ΓSpecIso_inv_comp_specMap_appTop f
  rw [Scheme.dualNumbersToSpec, Scheme.dualNumbersToSpec, Scheme.toSpecΓ_naturality_assoc,
    Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  have e₀ : (Spec.map f).dualNumbers.appTop =
      CommRingCat.ofHom (DualNumber.mapRingHom (Spec.map f).appTop.hom) :=
    CommRingCat.hom_ext (RingHom.ext fun a ↦ Scheme.Hom.dualNumbers_appTop_apply (Spec.map f) a)
  rw [e₀, ← CommRingCat.ofHom_comp, ← DualNumber.mapRingHom_comp, ← CommRingCat.ofHom_comp,
    ← DualNumber.mapRingHom_comp, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp, h]

variable (k) in
/-- The isomorphism `(Spec k[ε])[δ] ⟶ Spec k[ε][δ]`, over `k`. -/
noncomputable def dualNumbersSpecDualNumbers :
    overDualNumbers ((Spec (.of (DualNumber k))).asOver (Spec (.of k))) ⟶
      (Spec (.of (DualNumber (DualNumber k)))).asOver (Spec (.of k)) :=
  Over.homMk (Scheme.dualNumbersToSpec (.of (DualNumber k))) (by
    have e : CommRingCat.ofHom (algebraMap k (DualNumber (DualNumber k))) =
        CommRingCat.ofHom (algebraMap k (DualNumber k)) ≫
          CommRingCat.ofHom (TrivSqZeroExt.inlHom (DualNumber k) (DualNumber k)) :=
      CommRingCat.hom_ext (RingHom.ext fun c ↦ TrivSqZeroExt.algebraMap_eq_inl' _ _ _ c)
    simp only [OverClass.asOver_hom, specOverSpec_over, overDualNumbers_hom]
    rw [e, Spec.map_comp, ← Category.assoc, Scheme.dualNumbersToSpec_comp_specMap]
    rfl)

theorem dualNumbersSpecDualNumbers_comp_eps :
    dualNumbersSpecDualNumbers k ≫ (Spec.map (CommRingCat.ofHom
      (DualNumber.liftElem (R := k) eps₂ eps₂_mul_self).toRingHom)).asOver (Spec (.of k)) =
        overDualNumbersProj _ := by
  have h : CommRingCat.ofHom (DualNumber.liftElem (R := k) eps₂ eps₂_mul_self).toRingHom =
      CommRingCat.ofHom (TrivSqZeroExt.inlHom (DualNumber k) (DualNumber k)) :=
    CommRingCat.hom_ext (RingHom.ext fun a ↦ by
      ext <;> simp [DualNumber.liftElem_apply, TrivSqZeroExt.algebraMap_eq_inl'])
  ext1
  simp only [dualNumbersSpecDualNumbers, Over.comp_left, Over.homMk_left,
    OverClass.asOverHom_left, overDualNumbersProj_left]
  rw [h]
  exact Scheme.dualNumbersToSpec_comp_specMap _

theorem dualNumbersSpecDualNumbers_comp_del :
    dualNumbersSpecDualNumbers k ≫ (Spec.map (CommRingCat.ofHom
      (DualNumber.liftElem (R := k) del₂ del₂_mul_self).toRingHom)).asOver (Spec (.of k)) =
        overDualNumbersToSpec _ := by
  have h : CommRingCat.ofHom (DualNumber.liftElem (R := k) del₂ del₂_mul_self).toRingHom =
      CommRingCat.ofHom (DualNumber.mapRingHom (algebraMap k (DualNumber k))) :=
    CommRingCat.hom_ext (RingHom.ext fun a ↦ by
      ext <;> simp [DualNumber.liftElem_apply, TrivSqZeroExt.algebraMap_eq_inl'])
  ext1
  simp only [dualNumbersSpecDualNumbers, overDualNumbersToSpec, Over.comp_left, Over.homMk_left,
    OverClass.asOverHom_left, OverClass.asOver_hom, specOverSpec_over]
  rw [h, Scheme.dualNumbersToSpec_naturality]
  rfl

/-- The element `ε` of `Γ(Spec k[ε], 𝒪)`. -/
noncomputable abbrev epsΓ : Γ(((Spec (.of (DualNumber k))).asOver (Spec (.of k))).left, ⊤) :=
  (Scheme.ΓSpecIso (.of (DualNumber k))).inv (inr 1)

theorem overDualNumbersScale_epsΓ_comp_toSpec :
    overDualNumbersScale _ (epsΓ (k := k)) ≫ overDualNumbersToSpec _ =
      dualNumbersSpecDualNumbers k ≫ (Spec.map (CommRingCat.ofHom
        (DualNumber.liftElem (R := k) (eps₂ * del₂) eps₂_mul_del₂_mul_self).toRingHom)).asOver
          (Spec (.of k)) := by
  have h : CommRingCat.ofHom (DualNumber.liftElem (R := k) (eps₂ * del₂)
      eps₂_mul_del₂_mul_self).toRingHom =
      CommRingCat.ofHom (DualNumber.liftElem (R := k) del₂ del₂_mul_self).toRingHom ≫
        CommRingCat.ofHom (DualNumber.scale (inr 1 : DualNumber k)).toRingHom :=
    CommRingCat.hom_ext (RingHom.ext fun a ↦ by
      ext <;> simp [DualNumber.liftElem_apply, TrivSqZeroExt.algebraMap_eq_inl'])
  rw [← dualNumbersSpecDualNumbers_comp_del]
  ext1
  simp only [dualNumbersSpecDualNumbers, Over.comp_left, Over.homMk_left,
    OverClass.asOverHom_left, overDualNumbersScale_left]
  rw [h, Spec.map_comp, ← Category.assoc, ← Category.assoc]
  exact congrArg (· ≫ Spec.map _)
    (Scheme.dualNumbersScale_comp_dualNumbersToSpec (.of (DualNumber k)) (inr 1))

omit [LocallyOfFiniteType G.hom] in
/-- **Conjugation by `1 + εx`.** On the infinitesimal points with values in `Spec k[ε]`, the
conjugation by the tangent point `1 + εx` of `x ∈ Lie(G)` is `y ↦ y + ε[x, y]`: it is the
commutator `(1 + εx)(1 + δy)(1 + εx)⁻¹(1 + δy)⁻¹ = 1 + εδ[x, y]` over `k[ε][δ]`. -/
theorem infPointsAtConj_tangentPoint (x y : Lie G) :
    infPointsAtConj (tangentPoint x) (lieAt _ y) =
      infPointsAtScale _ (epsΓ (k := k)) (lieAt _ ⁅x, y⁆) * lieAt _ y := by
  have hE : overDualNumbersProj _ ≫ tangentPoint x =
      dualNumbersSpecDualNumbers k ≫ (tangentEps (lieEquivTangent G x)).1 := by
    rw [← dualNumbersSpecDualNumbers_comp_eps, Category.assoc]
    rfl
  have hD : (lieAt _ y).1 =
      dualNumbersSpecDualNumbers k ≫ (tangentDel (lieEquivTangent G y)).1 := by
    rw [coe_lieAt, ← dualNumbersSpecDualNumbers_comp_del, Category.assoc]
    rfl
  have hM : (infPointsAtScale _ (epsΓ (k := k)) (lieAt _ ⁅x, y⁆)).1 =
      dualNumbersSpecDualNumbers k ≫ (tangentMul (lieEquivTangent G ⁅x, y⁆)).1 := by
    rw [coe_infPointsAtScale, coe_lieAt, ← Category.assoc, overDualNumbersScale_epsΓ_comp_toSpec,
      Category.assoc]
    rfl
  have hc : (tangentMul (lieEquivTangent G ⁅x, y⁆)).1 =
      (tangentEps (lieEquivTangent G x)).1 * (tangentDel (lieEquivTangent G y)).1 *
        (tangentEps (lieEquivTangent G x)).1⁻¹ * (tangentDel (lieEquivTangent G y)).1⁻¹ := by
    rw [lieEquivTangent_lie, tangentMul_tangentBracket, commutatorElement_def]
    rfl
  apply Subtype.ext
  rw [coe_infPointsAtConj, Subgroup.coe_mul, hE, hD, hM, hc, ← GrpObj.comp_inv,
    ← MonObj.comp_mul, ← MonObj.comp_mul, ← MonObj.comp_mul]
  congr 1
  group

/-- **The differential of the adjoint representation is the adjoint representation of the Lie
algebra**: `d Ad = ad`, that is `Ad(1 + εx)(y) = y + ε[x, y]`. (blueprint:
`lemma-stable-subspaces-center`) -/
theorem differential_adjoint (x : Lie G) :
    GeneralLinearGroup.RationalHom.differential (adjoint b) x =
      LinearMap.toMatrix b b (LieAlgebra.ad k (Lie G) x) := by
  rw [GeneralLinearGroup.RationalHom.differential_eq_map_snd,
    GeneralLinearGroup.RationalHom.points_apply]
  ext i j
  have hij := homGLEquiv_asOver_apply I (tangentPoint x ≫ adjoint b) i j
  rw [homGLEquiv_comp_adjoint, coe_adjointHom] at hij
  have hz := congrArg (Scheme.ΓSpecIso (.of (DualNumber k))).hom hij
  rw [Iso.inv_hom_id_apply] at hz
  rw [Matrix.map_apply, ← hz, LinearMap.toMatrix_apply, LieAlgebra.ad_apply, adjointMatrix_apply,
    infPointsAtConj_tangentPoint, infPointsAtCoord_mul, infPointsAtCoord_infPointsAtScale,
    infPointsAtCoord_lieAt, infPointsAtCoord_lieAt]
  have hσ (c : k) : overΓAlgebraMap ((Spec (.of (DualNumber k))).asOver (Spec (.of k))) c =
      (Scheme.ΓSpecIso (.of (DualNumber k))).inv (inl c) :=
    congrArg (fun f ↦ f c)
      (Scheme.ΓSpecIso_inv_comp_specMap_appTop (CommRingCat.ofHom (algebraMap k (DualNumber k))))
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hσ, epsΓ]
  have key (z w v : DualNumber k) : (Scheme.ΓSpecIso (.of (DualNumber k))).hom
      ((Scheme.ΓSpecIso (.of (DualNumber k))).inv z * (Scheme.ΓSpecIso (.of (DualNumber k))).inv w +
        (Scheme.ΓSpecIso (.of (DualNumber k))).inv v) = z * w + v := by
    rw [map_add, map_mul, Iso.inv_hom_id_apply, Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]
  refine (congrArg TrivSqZeroExt.snd (key (inr 1) (inl _) (inl _))).trans ?_
  simp

/-- A tangent vector is killed by `d Ad = ad` if and only if it is central in `Lie(G)`. -/
theorem differential_adjoint_eq_zero_iff (x : Lie G) :
    differential (adjoint b) x = 0 ↔ x ∈ LieAlgebra.center k (Lie G) := by
  have h1 : differential (adjoint b) x = 0 ↔
      GeneralLinearGroup.RationalHom.differential (adjoint b) x = 0 := by
    rw [GeneralLinearGroup.RationalHom.differential_apply]
    exact EmbeddingLike.map_eq_zero_iff.symm
  rw [h1, differential_adjoint, LinearEquiv.map_eq_zero_iff]
  change _ ↔ x ∈ LieModule.maxTrivSubmodule k (Lie G) (Lie G)
  rw [LieModule.mem_maxTrivSubmodule]
  refine ⟨fun h y ↦ ?_, fun h ↦ LinearMap.ext fun y ↦ ?_⟩
  · have h' := LinearMap.congr_fun h y
    rw [LieAlgebra.ad_apply, LinearMap.zero_apply] at h'
    rw [← lie_skew, h', neg_zero]
  · rw [LieAlgebra.ad_apply, LinearMap.zero_apply, ← lie_skew, h y, neg_zero]

/-- **The Lie algebra of the kernel of `Ad` is the centre of `Lie(G)`**: `Lie(ker Ad) = ker(ad)`,
and `ker(ad) = 𝔷(Lie G)`. (blueprint: `lemma-stable-subspaces-center`) -/
theorem mem_range_differential_kerι_adjoint_iff (x : Lie G) :
    x ∈ (differential (CategoryTheory.GrpObj.kerι (adjoint b))).range ↔
      x ∈ LieAlgebra.center k (Lie G) :=
  (mem_range_differential_kerι_iff _ x).trans (differential_adjoint_eq_zero_iff b x)

end DifferentialAdjoint

end GrpObj

end AlgebraicGeometry
