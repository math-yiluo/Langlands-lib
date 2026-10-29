import Langlands.AlgebraicGeometry.Picard.RigidifiedIsoUniquenessStatement
import Langlands.AlgebraicGeometry.Picard.LineBundleDualEvaluation
import Langlands.AlgebraicGeometry.ModuleLinear
import Langlands.AlgebraicGeometry.ModuleLocalHomPullbackProofs
import Langlands.AbelianScheme.RelativeGlobalUnits

/-! # Uniqueness of rigidified isomorphisms of abelian-scheme line bundles -/

open CategoryTheory AlgebraicGeometry Opposite
open Langlands.AlgebraicGeometry.Picard (IsLocallyFreeRankOne)

set_option backward.isDefEq.respectTransparency false

universe u

noncomputable section

namespace Langlands.Scheme.Modules

section Classification

variable {X : AlgebraicGeometry.Scheme.{u}} {M : X.Modules} {W : X.Opens}
  (t : M.restrict W.ι ≅ SheafOfModules.unit W.toScheme.ringCatSheaf)

/-- The coordinate of a section over an open `V ⊆ W` with respect to the local generator
`trivGen t i` of a trivialization. -/
def trivCoord {V : X.Opens} (i : V ⟶ W) : Γ(M, V) →ₗ[Γ(X, V)] Γ(X, V) :=
  dualEval M V ((dual M).presheaf.map i.op (trivDualGen t))

lemma trivCoord_smul_trivGen {V : X.Opens} (i : V ⟶ W) (m : Γ(M, V)) :
    trivCoord t i m • trivGen t i = m :=
  trivGen_expansion t i m

lemma trivCoord_trivGen {V : X.Opens} (i : V ⟶ W) : trivCoord t i (trivGen t i) = 1 :=
  trivDualGen_eval t i

/-- Coefficients with respect to a local generator are unique. -/
lemma smul_trivGen_injective {V : X.Opens} (i : V ⟶ W) {a b : Γ(X, V)}
    (h : a • trivGen t i = b • trivGen t i) : a = b := by
  have h' := congrArg (trivCoord t i) h
  rw [map_smul, map_smul, trivCoord_trivGen, smul_eq_mul, smul_eq_mul, mul_one,
    mul_one] at h'
  exact h'

/-- The scalar by which an endomorphism acts on the local generator of a trivialization. -/
def localScalar (φ : M ⟶ M) : Γ(X, W) :=
  trivCoord t (𝟙 W) (φ.app W (trivGen t (𝟙 W)))

/-- Over every open contained in a trivializing open, an endomorphism is multiplication by
the restriction of its local scalar. -/
lemma app_eq_localScalar_smul (φ : M ⟶ M) {V : X.Opens} (i : V ⟶ W) (m : Γ(M, V)) :
    φ.app V m = X.presheaf.map i.op (localScalar t φ) • m := by
  have hg : trivGen t i = M.presheaf.map i.op (trivGen t (𝟙 W)) := by
    rw [trivGen_restrict, Category.comp_id]
  have h1 : φ.app V (trivGen t i) = X.presheaf.map i.op (localScalar t φ) • trivGen t i := by
    rw [hg]
    refine (PresheafOfModules.naturality_apply φ.val i.op (trivGen t (𝟙 W))).trans ?_
    change M.presheaf.map i.op (φ.app W (trivGen t (𝟙 W))) = _
    conv_lhs => rw [← trivCoord_smul_trivGen t (𝟙 W) (φ.app W (trivGen t (𝟙 W)))]
    rw [Scheme.Modules.map_smul]
    rfl
  conv_lhs => rw [← trivCoord_smul_trivGen t i m]
  rw [Scheme.Modules.Hom.app_smul, h1, smul_smul, mul_comm, ← smul_smul,
    trivCoord_smul_trivGen]

end Classification

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- Every endomorphism of a locally free module sheaf of rank one is multiplication by a
global function. -/
theorem exists_eq_smul_id_of_isLocallyFreeRankOne {M : X.Modules}
    (hM : IsLocallyFreeRankOne M) (φ : M ⟶ M) : ∃ c : Γ(X, ⊤), φ = c • 𝟙 M := by
  choose W hxW t using hM
  let d : ∀ x : X, Γ(X, W x) := fun x ↦ localScalar (t x).some φ
  have hcomp : TopCat.Presheaf.IsCompatible X.sheaf.1 W d := by
    intro x y
    apply smul_trivGen_injective (t x).some (homOfLE inf_le_left)
    exact (app_eq_localScalar_smul (t x).some φ (homOfLE inf_le_left) _).symm.trans
      (app_eq_localScalar_smul (t y).some φ (homOfLE inf_le_right) _)
  obtain ⟨c, hc, -⟩ := X.sheaf.existsUnique_gluing' W ⊤ (fun _ ↦ homOfLE le_top)
    (fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxW x⟩) d hcomp
  have hc' : ∀ x, X.presheaf.map (homOfLE le_top).op c = localScalar (t x).some φ := hc
  refine ⟨c, ?_⟩
  ext U m
  change φ.app U m = restrictScalar U c • m
  refine TopCat.Sheaf.eq_of_locally_eq' (F := ⟨M.presheaf, M.isSheaf⟩) (fun x ↦ U ⊓ W x) U
    (fun _ ↦ homOfLE inf_le_left) (fun x hx ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx, hxW x⟩) _ _
    fun x ↦ ?_
  have hnat := PresheafOfModules.naturality_apply φ.val
    (homOfLE (inf_le_left : U ⊓ W x ≤ U)).op m
  change φ.app _ (M.presheaf.map _ m) = M.presheaf.map _ (φ.app U m) at hnat
  change M.presheaf.map (homOfLE inf_le_left).op (φ.app U m) =
    M.presheaf.map (homOfLE inf_le_left).op (restrictScalar U c • m)
  rw [← hnat, app_eq_localScalar_smul (t x).some φ (homOfLE inf_le_right),
    Scheme.Modules.map_smul, ← hc' x]
  congr 1
  change X.presheaf.map _ (restrictScalar (W x) c) = X.presheaf.map _ (restrictScalar U c)
  rw [restrictScalar_map, restrictScalar_map]

end Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

open Langlands.SchemeModule

variable {S X : AlgebraicGeometry.Scheme.{u}} {ε : S ⟶ X}

/-- Restricting a global function to the whole space does nothing. -/
lemma restrictScalar_top (r : Γ(S, ⊤)) : Langlands.Scheme.Modules.restrictScalar ⊤ r = r := by
  change S.presheaf.map (𝟙 (⊤ : S.Opens)).op r = r
  rw [op_id, S.presheaf.map_id]
  rfl

/-- If the rigidifying morphism is injective on global functions, then every endomorphism of
a rigidified line bundle is the identity. -/
theorem endo_eq_id (hε : Function.Injective ε.appTop) (L : RigidifiedLineBundle ε)
    (φ : L ⟶ L) : φ = 𝟙 L := by
  obtain ⟨c, hc⟩ :=
    Langlands.Scheme.Modules.exists_eq_smul_id_of_isLocallyFreeRankOne L.property φ.hom.val
  have h := φ.hom.property
  rw [hc, Langlands.Scheme.Modules.pullback_map_smul, CategoryTheory.Functor.map_id,
    Linear.comp_smul, Category.comp_id] at h
  have h2 : ε.appTop c • 𝟙 (structureModule S) = 𝟙 (structureModule S) := by
    have h' := congrArg (· ≫ L.obj.rigidification.inv) h
    simpa only [Linear.smul_comp, Iso.hom_inv_id] using h'
  have h3 := congrArg (fun g ↦ g.app ⊤ (1 : Γ(S, ⊤))) h2
  change Langlands.Scheme.Modules.restrictScalar ⊤ (ε.appTop c) * 1 = 1 at h3
  rw [restrictScalar_top, mul_one] at h3
  have hc1 : c = 1 := hε (h3.trans (map_one ε.appTop.hom).symm)
  apply ObjectProperty.hom_ext
  apply Subtype.ext
  rw [hc, hc1, one_smul]
  rfl

end Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- The unit section of the base change of an abelian scheme is injective on global functions,
because the projection to the test scheme is an isomorphism on global functions. -/
lemma relativeSection_appTop_injective {S : AlgebraicGeometry.Scheme.{u}} (A : AbelianScheme S)
    (T : Over S) :
    Function.Injective
      ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T).appTop := by
  have hs := congrArg Scheme.Hom.appTop
    (relativeSection_projection A.X.hom (unitSection A) (unitSection_comp A) T)
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop] at hs
  have := universalGlobalFunctions A T
  have he := IsIso.eq_inv_of_hom_inv_id hs
  have h2 : ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T).appTop ≫
      ((relativeProjection A.X.hom).app T).appTop = 𝟙 _ := by
    rw [he, IsIso.inv_hom_id]
  refine Function.LeftInverse.injective (g := ((relativeProjection A.X.hom).app T).appTop) ?_
  intro x
  rw [← ConcreteCategory.comp_apply, h2]
  rfl

/-- Any two rigidified isomorphisms between actual relative rigidified line bundles agree. -/
theorem rigidifiedIsoUniqueness : RigidifiedIsoUniquenessStatement.{u} := by
  intro S A T L M
  refine ⟨fun e e' ↦ Iso.ext ?_⟩
  have h := RigidifiedLineBundle.endo_eq_id (relativeSection_appTop_injective A T) L
    (e.hom ≫ e'.inv)
  calc e.hom = (e.hom ≫ e'.inv) ≫ e'.hom := by simp
    _ = e'.hom := by rw [h, Category.id_comp]

end Langlands.AbelianScheme
