import Langlands.AbelianScheme.LieAdditivityStatement
import Langlands.AlgebraicGeometry.RelativeDerivationsPullback

/-!
# Additivity of the relative Lie differential

The cotangent map at the identity of a group-scheme homomorphism into a commutative group
scheme is additive in the homomorphism. Dualizing gives additivity of the Lie differential.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
  MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

variable {S : AlgebraicGeometry.Scheme.{u}}

open Langlands.Scheme

/-- Relative derivations along the identity of the base vanish. -/
lemma relativeDerivation_app_eq_zero_of_id {M : S.Modules}
    (d : RelativeDerivation (𝟙 S) M) (U : S.Opens) (a : Γ(S, U)) : d.app U a = 0 := by
  exact d.app_base U a

/-- The cotangent module at the identity of the trivial group scheme is zero. -/
lemma isZero_cotangentAtIdentity_tensorUnit :
    Limits.IsZero (𝟙_ (GroupScheme S)).cotangentAtIdentity := by
  have h : Limits.IsZero (relativeDifferentials (𝟙 S)) := by
    rw [Limits.IsZero.iff_id_eq_zero]
    apply relativeDifferentials_hom_ext
    ext U a
    exact (relativeDerivation_app_eq_zero_of_id _ U.unop a).trans
      (relativeDerivation_app_eq_zero_of_id _ U.unop a).symm
  exact Functor.map_isZero _ h

/-- The cotangent map of the trivial homomorphism vanishes. -/
lemma cotangentMap_one {G H : GroupScheme S} [IsCommMonObj H.X] :
    cotangentMap (1 : G ⟶ H) = 0 := by
  rw [Hom.one_def, cotangentMap_comp, isZero_cotangentAtIdentity_tensorUnit.eq_of_src
    (cotangentMap (toUnit G)) 0, comp_zero]

/-- If the cotangent map of `p` composed with `γ` vanishes, the derivation obtained from the
adjoint of `γ` kills every section pulled back along `p`. -/
lemma adjoint_derivation_app_map_eq_zero {G H : GroupScheme S} {M : S.Modules}
    (p : G ⟶ H) (γ : G.cotangentAtIdentity ⟶ M) (hp : cotangentMap p ≫ γ = 0)
    (U : H.X.left.Opens) (a : Γ(H.X.left, U)) :
    (RelativeDerivation.postcomp (relativeDifferentialsDerivation G.X.hom)
      ((pullbackPushforwardAdjunction G.identitySection).homEquiv _ _ γ)).app
        (p.hom.hom.left ⁻¹ᵁ U) (p.hom.hom.left.app U a) = 0 := by
  let A := pullbackPushforwardAdjunction G.identitySection
  have h1 : (Scheme.Modules.pullback G.identitySection).map
      (relativeDifferentialsMap p.hom.hom.left p.hom.hom.w) ≫ γ = 0 := by
    rw [← cancel_epi ((identityPullbackIso p).hom.app (relativeDifferentials H.X.hom)),
      comp_zero, ← Category.assoc]
    exact hp
  have h2 : relativeDifferentialsMap p.hom.hom.left p.hom.hom.w ≫ A.homEquiv _ _ γ = 0 := by
    rw [← A.homEquiv_naturality_left, h1, Adjunction.homEquiv_unit, Functor.map_zero,
      comp_zero]
  let B := pullbackPushforwardAdjunction p.hom.hom.left
  have h3 : B.homEquiv _ _ (relativeDifferentialsMap p.hom.hom.left p.hom.hom.w) ≫
      (pushforward p.hom.hom.left).map (A.homEquiv _ _ γ) = 0 := by
    rw [← B.homEquiv_naturality_right, h2, Adjunction.homEquiv_unit, Functor.map_zero,
      comp_zero]
  have h4 : ((pushforward p.hom.hom.left).map (A.homEquiv _ _ γ)).app U
      ((B.homEquiv _ _ (relativeDifferentialsMap p.hom.hom.left p.hom.hom.w)).app U
        ((relativeDifferentialsDerivation H.X.hom).app U a)) = 0 :=
    congrArg (fun φ => φ.app U ((relativeDifferentialsDerivation H.X.hom).app U a)) h3
  rw [relativeDifferentialsMap_adjoint_app] at h4
  exact h4

/-- A morphism out of the cotangent module of the actual group-scheme product `H ⊗ H` that is
killed by the cotangent maps of both projections vanishes. -/
lemma cotangentMap_fst_snd_ext {H : GroupScheme S} {M : S.Modules}
    (γ : (H ⊗ H).cotangentAtIdentity ⟶ M)
    (h₁ : cotangentMap (fst H H) ≫ γ = 0) (h₂ : cotangentMap (snd H H) ≫ γ = 0) :
    γ = 0 := by
  let A := pullbackPushforwardAdjunction (H ⊗ H).identitySection
  suffices hγ' : A.homEquiv _ _ γ = 0 by
    have hγ : γ = (A.homEquiv _ _).symm (A.homEquiv _ _ γ) :=
      ((A.homEquiv _ _).symm_apply_apply γ).symm
    rw [hγ, hγ', Adjunction.homEquiv_counit, Functor.map_zero, zero_comp]
  have hP : IsPullback (fst H H).hom.hom.left (snd H H).hom.hom.left H.X.hom H.X.hom := by
    rw [Grp.fst_hom_hom, Grp.snd_hom_hom, Over.fst_left, Over.snd_left]
    exact IsPullback.of_hasPullback H.X.hom H.X.hom
  have hd := RelativeDerivation.app_eq_zero_of_isPullback hP _
    (adjoint_derivation_app_map_eq_zero (fst H H) γ h₁)
    (adjoint_derivation_app_map_eq_zero (snd H H) γ h₂)
  apply relativeDifferentials_hom_ext
  ext V b
  refine (hd V.unop b).trans ?_
  change 0 = (RelativeDerivation.postcomp _ (0 : _ ⟶ _)).app V.unop b
  rw [RelativeDerivation.postcomp_app]
  simp

/-- Precomposing the hom-group product `fst * snd : H ⊗ H ⟶ H` with `lift f g` gives `f * g`. -/
lemma lift_comp_fst_mul_snd {G H : GroupScheme S} [IsCommMonObj H.X] (f g : G ⟶ H) :
    lift f g ≫ (fst H H * snd H H) = f * g := by
  rw [MonObj.comp_mul, lift_fst, lift_snd]

/-- The cotangent maps of the two coordinate inclusions `lift (𝟙 H) 1` and `lift 1 (𝟙 H)`,
followed by those of the projections, add up to the identity of the cotangent module of
`H ⊗ H`. -/
lemma cotangentMap_lift_fst_add_lift_snd {H : GroupScheme S} [IsCommMonObj H.X] :
    cotangentMap (lift (𝟙 H) (1 : H ⟶ H)) ≫ cotangentMap (fst H H) +
      cotangentMap (lift (1 : H ⟶ H) (𝟙 H)) ≫ cotangentMap (snd H H) = 𝟙 _ := by
  rw [← sub_eq_zero]
  apply cotangentMap_fst_snd_ext
  · rw [Preadditive.comp_sub, Preadditive.comp_add, ← Category.assoc, ← Category.assoc,
      ← cotangentMap_comp (lift (𝟙 H) (1 : H ⟶ H)), ← cotangentMap_comp (lift (1 : H ⟶ H) (𝟙 H)),
      lift_fst, lift_fst, cotangentMap_id, cotangentMap_one, Category.id_comp, zero_comp, add_zero,
      Category.comp_id, sub_self]
  · rw [Preadditive.comp_sub, Preadditive.comp_add, ← Category.assoc, ← Category.assoc,
      ← cotangentMap_comp (lift (𝟙 H) (1 : H ⟶ H)), ← cotangentMap_comp (lift (1 : H ⟶ H) (𝟙 H)),
      lift_snd, lift_snd, cotangentMap_id, cotangentMap_one, Category.id_comp, zero_comp, zero_add,
      Category.comp_id, sub_self]

/-- The cotangent map of the multiplication `fst * snd : H ⊗ H ⟶ H` of a commutative group
scheme is the sum of the cotangent maps of the two projections. -/
lemma cotangentMap_fst_mul_snd {H : GroupScheme S} [IsCommMonObj H.X] :
    cotangentMap (fst H H * snd H H) = cotangentMap (fst H H) + cotangentMap (snd H H) := by
  have h₁ : cotangentMap (fst H H * snd H H) ≫ cotangentMap (lift (𝟙 H) (1 : H ⟶ H)) = 𝟙 _ := by
    rw [← cotangentMap_comp, lift_comp_fst_mul_snd, mul_one, cotangentMap_id]
  have h₂ : cotangentMap (fst H H * snd H H) ≫ cotangentMap (lift (1 : H ⟶ H) (𝟙 H)) = 𝟙 _ := by
    rw [← cotangentMap_comp, lift_comp_fst_mul_snd, one_mul, cotangentMap_id]
  rw [← Category.comp_id (cotangentMap (fst H H * snd H H)), ← cotangentMap_lift_fst_add_lift_snd,
    Preadditive.comp_add, ← Category.assoc, ← Category.assoc, h₁, h₂, Category.id_comp,
    Category.id_comp]

/-- The cotangent map is additive in a homomorphism into a commutative group scheme. -/
lemma cotangentMap_mul {G H : GroupScheme S} [IsCommMonObj H.X] (f g : G ⟶ H) :
    cotangentMap (f * g) = cotangentMap f + cotangentMap g := by
  rw [← lift_comp_fst_mul_snd f g, cotangentMap_comp, cotangentMap_fst_mul_snd,
    Preadditive.add_comp, ← cotangentMap_comp, ← cotangentMap_comp, lift_fst, lift_snd]

/-- The Lie differential of the trivial homomorphism vanishes. -/
lemma lieMap_one {G H : GroupScheme S} [IsCommMonObj H.X] :
    lieMap (1 : G ⟶ H) = 0 := by
  rw [lieMap, cotangentMap_one, Langlands.Scheme.Modules.dualMap_zero]

/-- The Lie differential is additive in a homomorphism into a commutative group scheme. -/
lemma lieMap_mul {G H : GroupScheme S} [IsCommMonObj H.X] (f g : G ⟶ H) :
    lieMap (f * g) = lieMap f + lieMap g := by
  rw [lieMap, cotangentMap_mul, Langlands.Scheme.Modules.dualMap_add]
  rfl

end Langlands.GroupScheme

namespace Langlands.CommGroupScheme

/-- Geometric additivity of the relative Lie differential. -/
theorem lieAdditivity (S : AlgebraicGeometry.Scheme.{u}) : LieAdditivityStatement S :=
  fun _ _ f g => GroupScheme.lieMap_mul (groupHom f) (groupHom g)

variable {S : AlgebraicGeometry.Scheme.{u}}

/-- The relative Lie functor on commutative group schemes is additive. -/
instance lieFunctor_additive (S : AlgebraicGeometry.Scheme.{u}) : (lieFunctor S).Additive where
  map_add {G H f g} := lieAdditivity S G H f g

lemma lieMap_add {G H : CommGroupScheme S} (f g : G ⟶ H) :
    lieMap (f + g) = lieMap f + lieMap g :=
  lieAdditivity S G H f g

lemma lieMap_zero (G H : CommGroupScheme S) : lieMap (0 : G ⟶ H) = 0 :=
  (lieFunctor S).map_zero G H

lemma lieMap_neg {G H : CommGroupScheme S} (f : G ⟶ H) : lieMap (-f) = -lieMap f :=
  (lieFunctor S).map_neg

lemma lieMap_sub {G H : CommGroupScheme S} (f g : G ⟶ H) :
    lieMap (f - g) = lieMap f - lieMap g :=
  (lieFunctor S).map_sub

end Langlands.CommGroupScheme

namespace Langlands.AbelianScheme

variable {S : AlgebraicGeometry.Scheme.{u}}

/-- The underlying homomorphism of commutative group schemes is additive. -/
lemma commHom_add {A B : AbelianScheme S} (f g : A ⟶ B) :
    commHom (f + g) = commHom f + commHom g :=
  rfl

/-- The relative Lie functor on abelian schemes is additive. -/
instance lieFunctor_additive (S : AlgebraicGeometry.Scheme.{u}) : (lieFunctor S).Additive where
  map_add {A B f g} := by
    change CommGroupScheme.lieMap (commHom (f + g)) =
      CommGroupScheme.lieMap (commHom f) + CommGroupScheme.lieMap (commHom g)
    rw [commHom_add]
    exact CommGroupScheme.lieAdditivity S _ _ (commHom f) (commHom g)

lemma lieMap_add {A B : AbelianScheme S} (f g : A ⟶ B) :
    lieMap (f + g) = lieMap f + lieMap g :=
  (lieFunctor S).map_add

lemma lieMap_zero (A B : AbelianScheme S) : lieMap (0 : A ⟶ B) = 0 :=
  (lieFunctor S).map_zero A B

lemma lieMap_neg {A B : AbelianScheme S} (f : A ⟶ B) : lieMap (-f) = -lieMap f :=
  (lieFunctor S).map_neg

lemma lieMap_sub {A B : AbelianScheme S} (f g : A ⟶ B) :
    lieMap (f - g) = lieMap f - lieMap g :=
  (lieFunctor S).map_sub

end Langlands.AbelianScheme
