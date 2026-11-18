import Langlands.GroupScheme.IdentityJetBaseChangeCoordinates

/-! # Actual jet sections in a supplied corepresenting algebra -/

noncomputable section
universe u

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.IdentityJet

open AffineCoordinates Corepresented

/-- Composition with a spectrum map is literal substitution in ambient coordinates. -/
theorem coordinateMap_comp_specMap {S : Scheme.{u}} (H : GroupScheme S)
    {A C : CommRingCat.{u}} (j : H.X.left ⟶ Spec C) (φ : A →+* C)
    (U : S.Opens) (a : A) :
    coordinateMap H (j ≫ Spec.map (CommRingCat.ofHom φ)) U a =
      coordinateMap H j U (φ a) := by
  have hn := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)) a
  have hh := ConcreteCategory.congr_hom
    (Scheme.Hom.appLE_comp_appLE j (Spec.map (CommRingCat.ofHom φ))
      ⊤ ⊤ (H.X.hom ⁻¹ᵁ U) (by simp) (by simp))
      ((Scheme.ΓSpecIso A).inv a)
  change j.appLE ⊤ (H.X.hom ⁻¹ᵁ U) _
      ((Spec.map (CommRingCat.ofHom φ)).appTop ((Scheme.ΓSpecIso A).inv a)) = _ at hh
  change (Scheme.ΓSpecIso C).inv (φ a) =
    (Spec.map (CommRingCat.ofHom φ)).appTop ((Scheme.ΓSpecIso A).inv a) at hn
  rw [← hn] at hh
  exact hh.symm

/-- The restricted global generator is restriction of the same group function. -/
theorem restrict_quotientCoordinates_mk {S : Scheme.{u}} (H : GroupScheme S)
    [IsAffineHom H.X.hom] {A : CommRingCat.{u}} (j : H.X.left ⟶ Spec A)
    (I : Ideal A) (hI : VanishesAtIdentity H j I) (n : ℕ)
    (U : S.Opens) (a : A) :
    (module H n).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
        (quotientCoordinates H j I hI n (Ideal.Quotient.mk _ a)) =
      (quotientMap H n).app U (coordinateMap H j U a) := by
  rw [quotientCoordinates_mk, jetCoordinateMap_restrict, jetCoordinateMap_eq]
  rfl

private theorem baseChangeJetEquiv_tmul_function {R : CommRingCat.{u}}
    (G : GroupScheme (Spec R)) [IsAffine G.X.left]
    {S : Scheme.{u}} (b : S ⟶ Spec R) (n : ℕ) (U : S.affineOpens)
    (a : Γ(S, U)) (c : algebra G) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    baseChangeJetEquiv G b n U (a ⊗ₜ[R] Ideal.Quotient.mk _ c) =
      a • (quotientMap ((GroupScheme.baseChange b).obj G) n).app U
        (coordinateMap ((GroupScheme.baseChange b).obj G)
          (ambientProjection G b (𝟙 _)) U c) := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom b U
  let : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
    change IsAffineHom (Limits.pullback.snd G.X.hom b)
    exact MorphismProperty.pullback_snd (P := @IsAffineHom) _ _ inferInstance
  rw [baseChangeJetEquiv_tmul_mk]
  apply congrArg (a • ·)
  exact restrict_quotientCoordinates_mk ((GroupScheme.baseChange b).obj G)
    (ambientProjection G b (𝟙 ((GroupScheme.baseChange b).obj G)))
    (augIdeal (corepresentation G))
    (ambientProjection_vanishesAtIdentity G b (𝟙 ((GroupScheme.baseChange b).obj G))) n U c

private theorem groupIso_inv_hom_left {S : Scheme.{u}}
    {G H : GroupScheme S} (ψ : H ≅ G) :
    ψ.inv.hom.hom.left ≫ ψ.hom.hom.hom.left = 𝟙 G.X.left :=
  congrArg (fun f : G ⟶ G => f.hom.hom.left) ψ.inv_hom_id

private theorem coordinateMap_of_comparison {S : Scheme.{u}} (H : GroupScheme S)
    {A C : CommRingCat.{u}} (j : H.X.left ⟶ Spec C) (k : H.X.left ⟶ Spec A)
    (φ : A →+* C) (hφ : j ≫ Spec.map (CommRingCat.ofHom φ) = k)
    (U : S.Opens) (a : A) :
    coordinateMap H j U (φ a) = coordinateMap H k U a :=
  (coordinateMap_comp_specMap H j φ U a).symm.trans
    (congrArg (fun k => coordinateMap H k U a) hφ)

private theorem ambientProjection_comp_comparison {R : CommRingCat.{u}}
    (G : GroupScheme (Spec R)) [IsAffine G.X.left]
    {B : CommRingCat.{u}} (j : G.X.left ⟶ Spec B) (φ : B →+* algebra G)
    (hφ : Spec.map (CommRingCat.ofHom φ) = (groupSchemeIso G).hom.hom.hom.left ≫ j)
    {S : Scheme.{u}} (b : S ⟶ Spec R) :
    ambientProjection G b (𝟙 ((GroupScheme.baseChange b).obj G)) ≫
      Spec.map (CommRingCat.ofHom φ) = Limits.pullback.fst G.X.hom b ≫ j := by
  rw [hφ]
  simp only [ambientProjection, Grp.id_hom_hom, Over.id_left, Category.id_comp,
    Category.assoc]
  rw [← Category.assoc (groupSchemeIso G).inv.hom.hom.left,
    groupIso_inv_hom_left, Category.id_comp]

variable {R : CommRingCat.{u}} (F : CommAlgCat R ⥤ GrpCat.{u})
  {B : CommAlgCat R} (e : (F ⋙ forget GrpCat).CorepresentableBy B)

local instance corepresentedIsAffine : IsAffine (groupScheme F e).X.left := by
  change IsAffine (Spec (CommRingCat.of B))
  infer_instance

/-- The supplied corepresenting algebra and the chosen coordinates of its actual group. -/
def corepresentedCoordinateEquiv : B ≃ₐ[R] algebra (groupScheme F e) :=
  CommAlgCat.algEquivOfIso
    (algSpec.fullyFaithful.preimageIso
      ((Grp.forget _).mapIso (groupSchemeIso (groupScheme F e)))).unop

/-- The algebra comparison is induced by the actual group comparison. -/
theorem spec_corepresentedCoordinateEquiv :
    Spec.map (CommRingCat.ofHom (corepresentedCoordinateEquiv F e).toAlgHom.toRingHom) =
      (groupSchemeIso (groupScheme F e)).hom.hom.hom.left := by
  have hh : (algSpec R).map
      (CommAlgCat.ofHom (corepresentedCoordinateEquiv F e).toAlgHom).op =
        (groupSchemeIso (groupScheme F e)).hom.hom.hom := by
    change (algSpec R).map
      (algSpec.fullyFaithful.preimageIso
        ((Grp.forget _).mapIso (groupSchemeIso (groupScheme F e)))).hom = _
    rw [Functor.FullyFaithful.preimageIso_hom, algSpec.fullyFaithful.map_preimage]
    rfl
  exact congrArg (fun a => a.left) hh

/-- The actual coordinate comparison preserves evaluation at the identity. -/
theorem corepresentedCoordinateEquiv_counit :
    ((LinearEmbedding.counit (corepresentation (groupScheme F e))).hom).comp
        (corepresentedCoordinateEquiv F e).toAlgHom =
      (LinearEmbedding.counit e).hom := by
  have hs : Spec.map (CommRingCat.ofHom
      (((LinearEmbedding.counit (corepresentation (groupScheme F e))).hom).comp
        (corepresentedCoordinateEquiv F e).toAlgHom).toRingHom) =
      Spec.map (CommRingCat.ofHom (LinearEmbedding.counit e).hom.toRingHom) := by
    change Spec.map (CommRingCat.ofHom (corepresentedCoordinateEquiv F e).toAlgHom.toRingHom ≫
      CommRingCat.ofHom
        (LinearEmbedding.counit (corepresentation (groupScheme F e))).hom.toRingHom) = _
    rw [Spec.map_comp, spec_corepresentedCoordinateEquiv,
      ← identitySection_eq_specMap_counit,
      identitySection_naturality, identitySection_eq_specMap_counit]
  exact AlgHom.coe_ringHom_injective
    (congrArg CommRingCat.Hom.hom (Spec.map_injective hs))

private theorem augmentedEquiv_ker {A C : Type u} [CommRing A] [CommRing C]
    [Algebra R A] [Algebra R C] (φ : A ≃ₐ[R] C)
    (εA : A →ₐ[R] R) (εC : C →ₐ[R] R)
    (h : εC.comp φ.toAlgHom = εA) :
    RingHom.ker εC = (RingHom.ker εA).map φ.toRingHom := by
  have hc : (RingHom.ker εC).comap φ.toRingHom = RingHom.ker εA := by
    ext z
    change εC (φ z) = 0 ↔ εA z = 0
    have hh := AlgHom.congr_fun h z
    change εC (φ z) = εA z at hh
    rw [hh]
  calc
    _ = ((RingHom.ker εC).comap φ.toRingHom).map φ.toRingHom :=
      (Ideal.map_comap_of_surjective φ.toRingHom φ.surjective _).symm
    _ = _ := by rw [hc]

/-- The supplied augmentation-power quotient in the actual group's chosen coordinates. -/
def corepresentedJetCoordinateEquiv (n : ℕ) :
    (B ⧸ augIdeal e ^ (n + 1)) ≃ₐ[R]
      algebra (groupScheme F e) ⧸
        augIdeal (corepresentation (groupScheme F e)) ^ (n + 1) :=
  Ideal.quotientEquivAlg _ _ (corepresentedCoordinateEquiv F e)
    (by
      rw [Ideal.map_pow]
      exact congrArg (fun I => I ^ (n + 1))
        (augmentedEquiv_ker (corepresentedCoordinateEquiv F e)
          (LinearEmbedding.counit e).hom
          (LinearEmbedding.counit (corepresentation (groupScheme F e))).hom
          (corepresentedCoordinateEquiv_counit F e)))

variable {S : Scheme.{u}} (b : S ⟶ Spec R)

/-- Actual jet sections after arbitrary base change, in the supplied coordinates. -/
def corepresentedBaseChangeJetEquiv (n : ℕ) (U : S.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    Γ(S, U) ⊗[R] (B ⧸ augIdeal e ^ (n + 1)) ≃ₗ[Γ(S, U)]
      Γ(module ((GroupScheme.baseChange b).obj (groupScheme F e)) n, U) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
  exact (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl Γ(S, U) Γ(S, U))
      (corepresentedJetCoordinateEquiv F e n).toLinearEquiv).trans
    (baseChangeJetEquiv (groupScheme F e) b n U)

/-- The supplied-coordinate comparison sends each pure tensor to its actual function. -/
theorem corepresentedBaseChangeJetEquiv_tmul_mk (n : ℕ) (U : S.affineOpens)
    (a : Γ(S, U)) (c : B) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    corepresentedBaseChangeJetEquiv F e b n U (a ⊗ₜ[R] Ideal.Quotient.mk _ c) =
      a • (quotientMap ((GroupScheme.baseChange b).obj (groupScheme F e)) n).app U
        (coordinateMap ((GroupScheme.baseChange b).obj (groupScheme F e))
          (Limits.pullback.fst (groupScheme F e).X.hom b) U c) := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom b U
  change baseChangeJetEquiv (groupScheme F e) b n U
    (a ⊗ₜ[R] corepresentedJetCoordinateEquiv F e n (Ideal.Quotient.mk _ c)) = _
  change baseChangeJetEquiv (groupScheme F e) b n U
    (a ⊗ₜ[R] Ideal.Quotient.mk _ (corepresentedCoordinateEquiv F e c)) = _
  rw [baseChangeJetEquiv_tmul_function]
  apply congrArg (a • ·)
  change (inclusion ((GroupScheme.baseChange b).obj (groupScheme F e)) n).app
    (((GroupScheme.baseChange b).obj (groupScheme F e)).X.hom ⁻¹ᵁ U) _ = _
  apply congrArg ((inclusion ((GroupScheme.baseChange b).obj (groupScheme F e)) n).app
    (((GroupScheme.baseChange b).obj (groupScheme F e)).X.hom ⁻¹ᵁ U))
  have hj := ambientProjection_comp_comparison (groupScheme F e) (𝟙 _)
    (corepresentedCoordinateEquiv F e).toAlgHom.toRingHom
    ((spec_corepresentedCoordinateEquiv F e).trans (Category.comp_id _).symm) b
  rw [Category.comp_id] at hj
  exact coordinateMap_of_comparison ((GroupScheme.baseChange b).obj (groupScheme F e))
    (ambientProjection (groupScheme F e) b (𝟙 _))
    (Limits.pullback.fst (groupScheme F e).X.hom b)
    (corepresentedCoordinateEquiv F e).toAlgHom.toRingHom hj U c

end Langlands.GroupScheme.IdentityJet
