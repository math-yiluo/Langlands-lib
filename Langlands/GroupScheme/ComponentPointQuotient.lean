import Langlands.GroupScheme.GeometricComponents
import Langlands.GroupScheme.InnerAutomorphism

/-! # Rational-point component quotients without smoothness -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IdentityComponent

variable {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))

/-- Rational sections whose actual scheme point belongs to the identity component.
This subgroup is defined without any smoothness or finiteness hypothesis. -/
def rationalIdentityKernel : Subgroup (rationalPoints G) where
  carrier := {x | pointComponent G x = pointComponent G 1}
  one_mem' := rfl
  mul_mem' {x y} hx hy := by
    change pointComponent G x = pointComponent G 1 at hx
    change pointComponent G y = pointComponent G 1 at hy
    change pointComponent G (x * y) = pointComponent G 1
    rw [← translationComponents_pointComponent, hy,
      translationComponents_pointComponent, mul_one, hx]
  inv_mem' {x} hx := by
    have h := congrArg (translationComponents G x⁻¹) hx
    rw [translationComponents_pointComponent, translationComponents_pointComponent,
      inv_mul_cancel, mul_one] at h
    exact h.symm

/-- Connectedness is preserved by actual inner automorphisms, so the rational
identity-component subgroup is normal even when the group is nonreduced. -/
instance rationalIdentityKernel_normal : (rationalIdentityKernel G).Normal where
  conj_mem x hx g := by
    let f := (G.innerIso g).hom
    have h := congrArg f.hom.hom.left.continuous.connectedComponentsMap hx
    change pointComponent G (x ≫ f.hom.hom) = pointComponent G (1 ≫ f.hom.hom) at h
    have hconst : G.constantPoint g (𝟙_ (Over (Spec (CommRingCat.of k)))) = g := by
      change (𝟙 _) ≫ g = g
      exact Category.id_comp g
    rw [MonObj.one_comp] at h
    dsimp only [f] at h
    rw [comp_innerIso_hom, hconst] at h
    exact h

/-- Rational points modulo those in the actual identity component. This is an
ordinary group quotient, with no scheme-quotient claim. -/
def ComponentPointQuotient := rationalPoints G ⧸ rationalIdentityKernel G

instance : Group (ComponentPointQuotient G) :=
  inferInstanceAs (Group (rationalPoints G ⧸ rationalIdentityKernel G))

/-- The quotient homomorphism to the rational-point component quotient. -/
def componentPointProjection : rationalPoints G →* ComponentPointQuotient G :=
  QuotientGroup.mk' (rationalIdentityKernel G)

theorem componentPointProjection_surjective :
    Function.Surjective (componentPointProjection G) :=
  QuotientGroup.mk'_surjective _

@[simp]
theorem ker_componentPointProjection :
    (componentPointProjection G).ker = rationalIdentityKernel G :=
  QuotientGroup.ker_mk' _

/-- Two rational points belong to the same component exactly when their quotient
lies in the rational identity-component subgroup. -/
theorem pointComponent_eq_iff_mem_rationalIdentityKernel (x y : rationalPoints G) :
    pointComponent G x = pointComponent G y ↔ x⁻¹ * y ∈ rationalIdentityKernel G := by
  change pointComponent G x = pointComponent G y ↔
    pointComponent G (x⁻¹ * y) = pointComponent G 1
  calc
    pointComponent G x = pointComponent G y ↔
        translationComponents G x⁻¹ (pointComponent G x) =
          translationComponents G x⁻¹ (pointComponent G y) :=
      (translationComponents G x⁻¹).injective.eq_iff.symm
    _ ↔ pointComponent G 1 = pointComponent G (x⁻¹ * y) := by
      rw [translationComponents_pointComponent, translationComponents_pointComponent,
        inv_mul_cancel]
    _ ↔ pointComponent G (x⁻¹ * y) = pointComponent G 1 := eq_comm

/-- The rational-point quotient embeds into the actual connected-component type. -/
def componentPointEmbedding :
    ComponentPointQuotient G ↪ _root_.ConnectedComponents G.X.left where
  toFun := Quotient.lift (pointComponent G) (by
    intro x y hxy
    exact (pointComponent_eq_iff_mem_rationalIdentityKernel G x y).mpr
      (QuotientGroup.leftRel_apply.mp hxy))
  inj' := by
    intro a b hab
    induction a using Quotient.inductionOn with
    | h x =>
      induction b using Quotient.inductionOn with
      | h y =>
        exact Quotient.sound (QuotientGroup.leftRel_apply.mpr
          ((pointComponent_eq_iff_mem_rationalIdentityKernel G x y).mp hab))

@[simp]
theorem componentPointEmbedding_projection (x : rationalPoints G) :
    componentPointEmbedding G (componentPointProjection G x) = pointComponent G x :=
  rfl

/-- Any actual open immersion onto the identity component identifies its rational
range subgroup with the topologically defined rational kernel. -/
theorem mem_rationalIdentityKernel_iff_lift
    {H : GroupScheme (Spec (CommRingCat.of k))} (i : H ⟶ G)
    [IsOpenImmersion i.hom.hom.left]
    (hi : Set.range i.hom.hom.left = identitySet G) (x : rationalPoints G) :
    x ∈ rationalIdentityKernel G ↔
      ∃ y : rationalPoints H, y ≫ i.hom.hom = x := by
  change pointComponent G x = pointComponent G 1 ↔ _
  change _root_.ConnectedComponents.mk (x.left (basePoint k)) =
    _root_.ConnectedComponents.mk (identityPoint G) ↔ _
  rw [_root_.ConnectedComponents.coe_eq_coe']
  constructor
  · intro hx
    have hrange : Set.range x.left ⊆ Set.range i.hom.hom.left := by
      rw [hi]
      rintro _ ⟨p, rfl⟩
      have hp : p = basePoint k :=
        @Subsingleton.elim (Spec (CommRingCat.of k)) _ p _
      simpa only [hp] using hx
    exact ⟨FiniteEtaleImage.liftOver i.hom.hom x hrange,
      FiniteEtaleImage.liftOver_fac _ _ _⟩
  · rintro ⟨y, rfl⟩
    change i.hom.hom.left (y.left (basePoint k)) ∈ identitySet G
    rw [← hi]
    exact Set.mem_range_self _

/-- Affine groups locally of finite type have finitely many actual components,
without a smoothness assumption. -/
theorem finite_connectedComponents_of_locallyOfFiniteType
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom] :
    Finite (_root_.ConnectedComponents G.X.left) := by
  let : IsLocallyNoetherian G.X.left :=
    LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  let : CompactSpace G.X.left := QuasiCompact.compactSpace_of_compactSpace G.X.hom
  let : DiscreteTopology (_root_.ConnectedComponents G.X.left) := by
    apply discreteTopology_iff_isOpen_singleton.mpr
    intro c
    obtain ⟨p, rfl⟩ := _root_.ConnectedComponents.surjective_coe c
    rw [← _root_.ConnectedComponents.isQuotientMap_coe.isOpen_preimage,
      connectedComponents_preimage_singleton]
    exact Langlands.AlgebraicGeometry.locallyNoetherianConnectedComponentOpen_proof G.X.left p
  exact finite_of_compact_of_discrete

instance finite_componentPointQuotient
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom] :
    Finite (ComponentPointQuotient G) := by
  let := finite_connectedComponents_of_locallyOfFiniteType G
  exact Finite.of_injective (componentPointEmbedding G) (componentPointEmbedding G).injective

/-- Over an algebraically closed field every actual component has a rational
section, so the rational-point quotient parametrizes all components. -/
def componentPointQuotientEquiv [IsAlgClosed k] [LocallyOfFiniteType G.X.hom] :
    ComponentPointQuotient G ≃ _root_.ConnectedComponents G.X.left :=
  Equiv.ofBijective (componentPointEmbedding G) ⟨(componentPointEmbedding G).injective, by
    intro c
    obtain ⟨x, rfl⟩ := pointComponent_surjective_of_isAlgClosed G c
    exact ⟨componentPointProjection G x, rfl⟩⟩

@[simp]
theorem componentPointQuotientEquiv_projection [IsAlgClosed k]
    [LocallyOfFiniteType G.X.hom] (x : rationalPoints G) :
    componentPointQuotientEquiv G (componentPointProjection G x) = pointComponent G x :=
  rfl

/-- The size of the algebraic-closure rational quotient is exactly the geometric
component cardinal in Nagata's statement. -/
theorem natCard_geometricComponents_eq_componentPointQuotient
    [LocallyOfFiniteType G.X.hom] :
    Nat.card (GeometricComponents k G) =
      Nat.card (ComponentPointQuotient (GaloisPointComparison.baseChanged k
        (AlgebraicClosure k) G)) := by
  let : LocallyOfFiniteType
      (GaloisPointComparison.baseChanged k (AlgebraicClosure k) G).X.hom :=
    inferInstanceAs (LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom
      (GaloisPointComparison.baseMap k (AlgebraicClosure k))))
  exact Nat.card_congr (componentPointQuotientEquiv
    (GaloisPointComparison.baseChanged k (AlgebraicClosure k) G)).symm

/-- Geometric component cardinality is finite in the full non-smooth affine
finite-type scope of Nagata's statement. -/
theorem finite_geometricComponents_of_locallyOfFiniteType
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom] :
    Finite (GeometricComponents k G) := by
  let : LocallyOfFiniteType
      (GaloisPointComparison.baseChanged k (AlgebraicClosure k) G).X.hom :=
    inferInstanceAs (LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom
      (GaloisPointComparison.baseMap k (AlgebraicClosure k))))
  let : IsAffineHom
      (GaloisPointComparison.baseChanged k (AlgebraicClosure k) G).X.hom :=
    inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom
      (GaloisPointComparison.baseMap k (AlgebraicClosure k))))
  exact finite_connectedComponents_of_locallyOfFiniteType
    (GaloisPointComparison.baseChanged k (AlgebraicClosure k) G)

end Langlands.GroupScheme.IdentityComponent
