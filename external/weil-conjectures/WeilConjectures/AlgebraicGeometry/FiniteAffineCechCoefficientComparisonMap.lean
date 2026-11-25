/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteAffineCechModel
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonMorphismGenerator
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonMorphismFaces
import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction

/-! # Canonical generators for affine coefficient comparison

Source: Stacks Project, Tags 02KE, 01I9 and 01IA.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Sections of an open-restricted direct image are sections on the corresponding
intersection. Source: Stacks Project, Tag 0097 (restriction and direct image). 
(blueprint: lem-pc-finite-affine-cech-coefficient-comparison-map)
-/
def coefficientSupportIso {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules)
    (W : X.Opens) (B : S.Opens) :
    Γ((pushforward (W.ι ≫ f)).obj (M.restrict W.ι), B) ≅
      Γ(M, W ⊓ f ⁻¹ᵁ B) :=
  M.presheaf.mapIso (eqToIso (show
    W ⊓ f ⁻¹ᵁ B = W.ι ''ᵁ ((W.ι ≫ f) ⁻¹ᵁ B) by
      rw [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
        Scheme.Opens.opensRange_ι])).op

/-- The support identification commutes with restrictions of the base open.
Source: Stacks Project, Tag 0097. 
(blueprint: lem-pc-finite-affine-cech-coefficient-comparison-map)
-/
theorem coefficientSupportIso_naturality {X S : Scheme.{u}} (f : X ⟶ S)
    (M : X.Modules) (W : X.Opens) {B C : S.Opens} (i : B ⟶ C)
    (s : Γ((pushforward (W.ι ≫ f)).obj (M.restrict W.ι), C)) :
    (coefficientSupportIso f M W B).hom
        (((pushforward (W.ι ≫ f)).obj (M.restrict W.ι)).presheaf.map i.op s) =
      M.presheaf.map (homOfLE (inf_le_inf le_rfl
        ((TopologicalSpace.Opens.map f.base).map i).le)).op
          ((coefficientSupportIso f M W C).hom s) := by
  change M.presheaf.map (eqToHom (show W ⊓ f ⁻¹ᵁ B = W.ι ''ᵁ ((W.ι ≫ f) ⁻¹ᵁ B) by
      rw [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
        Scheme.Opens.opensRange_ι])).op
    (M.presheaf.map (homOfLE (W.ι.image_mono
      ((TopologicalSpace.Opens.map (W.ι ≫ f).base).map i).le)).op s) =
    M.presheaf.map (homOfLE (inf_le_inf le_rfl
      ((TopologicalSpace.Opens.map f.base).map i).le)).op
        (M.presheaf.map (eqToHom (show W ⊓ f ⁻¹ᵁ C = W.ι ''ᵁ ((W.ι ≫ f) ⁻¹ᵁ C) by
      rw [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
        Scheme.Opens.opensRange_ι])).op s)
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- The support identification transports the structural scalar action.
Source: Stacks Project, Tag 0097. 
(blueprint: lem-pc-finite-affine-cech-coefficient-comparison-map)
-/
theorem coefficientSupportIso_smul {X S : Scheme.{u}} (f : X ⟶ S)
    (M : X.Modules) (W : X.Opens) (B : S.Opens) (b : Γ(S, B))
    (s : Γ((pushforward (W.ι ≫ f)).obj (M.restrict W.ι), B)) :
    (coefficientSupportIso f M W B).hom (b • s) =
      X.presheaf.map (homOfLE (inf_le_right : W ⊓ f ⁻¹ᵁ B ≤ f ⁻¹ᵁ B)).op
        (f.app B b) • (coefficientSupportIso f M W B).hom s := by
  change M.presheaf.map (eqToHom (show
    W ⊓ f ⁻¹ᵁ B = W.ι ''ᵁ (W.ι ⁻¹ᵁ (f ⁻¹ᵁ B)) by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι])).op
    (((W.ι.appIso (W.ι ⁻¹ᵁ (f ⁻¹ᵁ B))).inv
      (W.ι.app (f ⁻¹ᵁ B) (f.app B b))) •
      (show Γ(M, W.ι ''ᵁ (W.ι ⁻¹ᵁ (f ⁻¹ᵁ B))) from s)) = _
  rw [map_smul]
  congr 1
  have h := congrArg (fun k ↦ k (f.app B b))
    (Scheme.Hom.app_appIso_inv W.ι (f ⁻¹ᵁ B))
  change (W.ι.appIso (W.ι ⁻¹ᵁ (f ⁻¹ᵁ B))).inv
    (W.ι.app (f ⁻¹ᵁ B) (f.app B b)) = _ at h
  rw [h]
  simp only [← ConcreteCategory.comp_apply, Category.assoc, ← Functor.map_comp]
  rfl

/-- The generator section of the pullback of an associated module.
Source: Stacks Project, Tags 01I9 and 01IA, adjunction units. 
(blueprint: lem-pc-finite-affine-cech-coefficient-comparison-map)
-/
def coefficientGenerator {S S' : Scheme.{u}} (g : S' ⟶ S)
    (N : ModuleCat.{u} Γ(S, ⊤)) (s : N) :
    Γ((pullback g).obj ((pullback S.toSpecΓ).obj (tilde N)), ⊤) :=
  let e := (tilde.toOpen N ⊤) s
  let e' := ((pullbackPushforwardAdjunction S.toSpecΓ).unit.app (tilde N)).app ⊤ e
  let e'' := ((pullback S.toSpecΓ).obj (tilde N)).presheaf.map
    (homOfLE (show ⊤ ≤ S.toSpecΓ ⁻¹ᵁ ⊤ by simp)).op e'
  ((pullback g).obj ((pullback S.toSpecΓ).obj (tilde N))).presheaf.map
    (homOfLE (show ⊤ ≤ g ⁻¹ᵁ ⊤ by simp)).op
      (((pullbackPushforwardAdjunction g).unit.app
        ((pullback S.toSpecΓ).obj (tilde N))).app ⊤ e'')

/-- The generator obtained by pulling a section back to an inverse-image open.
Source: Stacks Project, Tag 0097, the pullback adjunction unit. 
(blueprint: lem-pc-finite-affine-cech-coefficient-comparison-map)
-/
def coefficientPullbackGenerator {X X' : Scheme.{u}} (F : X.Modules)
    (U : X.Opens) (Z : U.toScheme.Opens) (g' : X' ⟶ X)
    (W : X'.Opens) (hW : W = g' ⁻¹ᵁ (U.ι ''ᵁ Z))
    (s : Γ(F.restrict U.ι, Z)) : Γ((pullback g').obj F, W) :=
  ((pullback g').obj F).presheaf.map (homOfLE hW.le).op
    (((pullbackPushforwardAdjunction g').unit.app F).app (U.ι ''ᵁ Z)
      ((F.restrictAppIso U.ι Z).hom s))

/-- Inverse image commutes with the nonempty intersections indexing coefficients.
Source: Stacks Project, Tag 02KE, the intersection calculation. 
(blueprint: lem-pc-finite-affine-cech-coefficient-comparison-map)
-/
theorem coefficientIntersection_preimage {X X' : Scheme.{u}} (U : X.Opens)
    {r : ℕ} (V : Fin r → U.toScheme.Opens) (g' : X' ⟶ X)
    (W : ULift.{u} (Fin r) → X'.Opens)
    (hW : ∀ i, W i = g' ⁻¹ᵁ (U.ι ''ᵁ V i.down))
    (p : ℕ) (t : Fin (p + 1) ↪o Fin r) :
    alternatingCechIntersection (fun i ↦ W ⟨i⟩) t =
      g' ⁻¹ᵁ (U.ι ''ᵁ alternatingCechIntersection V t) := by
  ext x
  simp only [alternatingCechIntersection, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
  constructor
  · intro hx
    have hx0 := hx 0
    rw [hW] at hx0
    obtain ⟨y, hy, he⟩ := hx0
    refine ⟨y, ?_, he⟩
    simp only [TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
    intro i
    have hxi := hx i
    rw [hW] at hxi
    obtain ⟨z, hz, hze⟩ := hxi
    have : z = y := U.ι.isOpenEmbedding.injective (hze.trans he.symm)
    simpa [this] using hz
  · rintro ⟨y, hy, he⟩ i
    rw [hW]
    refine ⟨y, ?_, he⟩
    exact (Set.mem_iInter.mp (show y ∈ ⋂ k, (V (t k) : Set U.toScheme) by
      simpa only [TopologicalSpace.Opens.coe_iInf] using hy)) i

/-- Canonical coefficient comparison morphisms and compatibility with a single face.
No invertibility is asserted, and no affine or quasi-coherence hypothesis is required.
Source: Stacks Project, Tag 02KE, the termwise map in Lemma 30.5.2; Tags 01I9,
01IA and 0097 for its construction from adjunction units.
(blueprint: lem-pc-finite-affine-cech-coefficient-comparison-map).

Proof: Put Y = f inverse image U and A = Gamma(U,O). For each open Z of Y,
form the module sheaf P_Z = (Z -> U)_*(F|Z). Restriction between opens gives
maps P_Z -> P_Z' in the direction of restriction of sections. The tilde/Gamma
counit over Spec A, followed by the pullback/direct-image counit of U -> Spec A,
gives a map from the associated A-module of F(Z) to P_Z. The scalar map in
this A-module is exactly the composite displayed in H, by naturality of the
canonical affine chart and GammaSpecIso. Pull this map back along g. The
adjoint-defined base-change morphism for Z -> U maps it into the direct image
of the pullback of F|Z. Pullback composition and open-immersion restriction
identify that module with M restricted to the inverse-image open W_Z. These
operations define q without any affineness assumption. The triangle identities
for the three adjunctions show that q sends the displayed generator to the
pullback unit applied to s. Naturality of the counit, restriction unit, and
base-change morphism under inclusions Z' <= Z gives the face equation.
Every identification uses the canonical composition comparisons, so the equation
is an equality of the actual restriction maps on sections. Empty opens have
zero sections and the same construction. With no increasing tuples the family
is empty. -/
theorem exists_coefficientComparison_maps {X T : Scheme.{u}} (f : X ⟶ T)
    (F : X.Modules) (U : T.Opens) {r : ℕ}
    (V : Fin r → (f ⁻¹ᵁ U).toScheme.Opens)
    {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
    (w : g' ≫ f = f' ≫ (g ≫ U.ι))
    (W₀ : ULift.{u} (Fin r) → X'.Opens)
    (hW : ∀ i, W₀ i = g' ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ''ᵁ V i.down)) :
    let G := (F.restrict (f ⁻¹ᵁ U).ι).presheafModuleCat
    let H := ModuleCat.restrictScalars
      (((Scheme.ΓSpecIso Γ(U.toScheme, ⊤)).inv ≫
        ((f ∣_ U) ≫ U.toScheme.toSpecΓ).appTop).hom) ⋙
      tilde.functor Γ(U.toScheme, ⊤) ⋙
      Modules.pullback U.toScheme.toSpecΓ ⋙ Modules.pullback g
    let M := (Modules.pullback g').obj F
    let W := fun (p : ℕ) (t : Fin (p + 1) ↪o Fin r) ↦
      alternatingCechIntersection (fun i ↦ W₀ ⟨i⟩) t
    ∃ q : ∀ (p : ℕ) (t : Fin (p + 1) ↪o Fin r),
      H.obj (G.obj (op (alternatingCechIntersection V t))) ⟶
        (pushforward ((W p t).ι ≫ f')).obj (M.restrict (W p t).ι),
      (∀ (p : ℕ) (t : Fin (p + 1) ↪o Fin r)
        (s : Γ(F.restrict (f ⁻¹ᵁ U).ι, alternatingCechIntersection V t)),
        (coefficientSupportIso f' M (W p t) ⊤).hom
          ((q p t).app ⊤ (coefficientGenerator g _ s)) =
        M.presheaf.map (homOfLE (inf_le_left : W p t ⊓ f' ⁻¹ᵁ ⊤ ≤ W p t)).op
          (coefficientPullbackGenerator F (f ⁻¹ᵁ U) (alternatingCechIntersection V t)
            g' (W p t) (coefficientIntersection_preimage _ V g' W₀ hW p t) s)) ∧
      (∀ (p : ℕ) (t : Fin (p + 2) ↪o Fin r) (j : Fin (p + 2)) (B : T'.Opens)
        (s : Γ(H.obj (G.obj (op (alternatingCechIntersection V
          ((Fin.succAboveOrderEmb j).trans t)))), B)),
        (coefficientSupportIso f' M (W (p + 1) t) B).hom
          ((q (p + 1) t).app B
            ((H.map (G.map (homOfLE
              (alternatingCechIntersection_face_le V p t j)).op)).app B s)) =
        M.presheaf.map (homOfLE (inf_le_inf
          (alternatingCechIntersection_face_le (fun i ↦ W₀ ⟨i⟩) p t j) le_rfl)).op
            ((coefficientSupportIso f' M (W p ((Fin.succAboveOrderEmb j).trans t)) B).hom
              ((q p ((Fin.succAboveOrderEmb j).trans t)).app B s))) := by
  let q := fun (p : ℕ) (t : Fin (p + 1) ↪o Fin r) ↦
    coefficientComparisonMorphism f F U (alternatingCechIntersection V t)
      g g' f' w (alternatingCechIntersection (fun i ↦ W₀ ⟨i⟩) t)
      (coefficientIntersection_preimage _ V g' W₀ hW p t)
  refine ⟨q, ?_, ?_⟩
  · intro p t s
    exact coefficientComparisonMorphism_generator f F U (alternatingCechIntersection V t)
      g g' f' w (alternatingCechIntersection (fun i ↦ W₀ ⟨i⟩) t)
      (coefficientIntersection_preimage _ V g' W₀ hW p t) s
  · exact coefficientComparisonMorphism_faces f F U V g g' f' w W₀
      (coefficientIntersection_preimage _ V g' W₀ hW)

end
end AlgebraicGeometry.Scheme.Modules
