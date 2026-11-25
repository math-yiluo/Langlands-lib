/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.AlgebraicGeometry.Sf.SfCompactSupportRestrictionOfScalars

import WeilConjectures.AlgebraicGeometry.FiniteCompactScalar.FiniteCompactSupportScalarTransport
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin

/-!
# The canonical finite coefficient comparison for compact support

Source: Stacks Tags 0F0G, 0GL1, 0GL6; blueprint finite compact support, Steps 7--10
(blueprint: lem-finite-compact-support-scalar-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem finite_homology_support_iff
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (K : DerivedCategory C) :
    Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor C i).obj K)} ↔
      ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, i < a ∨ b < i →
        IsZero ((DerivedCategory.homologyFunctor C i).obj K) := by
  classical
  constructor
  · intro h
    obtain ⟨a, ha⟩ := h.bddBelow
    obtain ⟨b, hb⟩ := h.bddAbove
    refine ⟨min a b, max a b, min_le_max, fun i hi ↦ ?_⟩
    by_contra hn
    rcases hi with hi | hi
    · exact (not_lt_of_ge (le_trans (min_le_left _ _) (ha hn))) hi
    · exact (not_lt_of_ge (le_trans (hb hn) (le_max_right _ _))) hi
  · rintro ⟨a, b, _, h⟩
    apply (Set.finite_Icc a b).subset
    intro i hi
    exact ⟨le_of_not_gt (fun hia ↦ hi (h i (Or.inl hia))),
      le_of_not_gt (fun hbi ↦ hi (h i (Or.inr hbi)))⟩

private def scalarMateTransformation
    {C₀ C₁ D₀ D₁ : Type*}
    [Category C₀] [Category C₁] [Category D₀] [Category D₁]
    {Sx : C₀ ⥤ C₁} {Rx : C₁ ⥤ C₀}
    {Sy : D₀ ⥤ D₁} {Ry : D₁ ⥤ D₀}
    (ax : Sx ⊣ Rx) (ay : Sy ⊣ Ry)
    (F : C₀ ⥤ D₀) (G : C₁ ⥤ D₁) (e : Rx ⋙ F ⟶ G ⋙ Ry) :
    F ⋙ Sy ⟶ Sx ⋙ G where
  app K := (ay.homEquiv _ _).symm
    (F.map (ax.unit.app K) ≫ e.app (Sx.obj K))
  naturality {K L} f := by
    apply (ay.homEquiv _ _).injective
    dsimp only [Functor.comp_map]
    rw [ay.homEquiv_naturality_left, ay.homEquiv_naturality_right,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rw [← Category.assoc, ← F.map_comp]
    have hu := ax.unit.naturality f
    change f ≫ ax.unit.app L = ax.unit.app K ≫ Rx.map (Sx.map f) at hu
    rw [hu]
    simp only [F.map_comp, Category.assoc]
    exact congrArg (fun q ↦ F.map (ax.unit.app K) ≫ q) (e.naturality (Sx.map f))

/-- A scheme of finite type over a field is noetherian. -/
private theorem noetherianOfField
    (K : Type u) [Field K] (Y : Scheme.{u}) [Y.Over (Spec (.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K))] [QuasiCompact (Y ↘ Spec (.of K))] :
    IsNoetherian Y := by
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of K))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of K))
  exact ⟨⟩

/-- The proper compactification space over a noetherian target is noetherian. -/
private theorem noetherianCompactification {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) [IsNoetherian Y] : IsNoetherian c.Z := by
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  exact ⟨⟩

/-- The canonical scalar-adjunction transpose for a fixed compactification is invertible
when the input and its ordinary derived reduction are bounded constructible.
Only invertibility is asserted here: constructibility and interval bounds are supplied
independently by finite compact-support finiteness.

Source: Stacks Tags 0F0G, 0GL1 and 0GL6; blueprint
theorem-results-from-etale-theory--3, Steps 7--10
(blueprint: lem-finite-compact-support-scalar-comparison).

Proof: descend K to a bounded constructible etale complex G by finite-ring
constructible origin. Exact fully faithful comparison, and its K-flat scalar
comparison, show that the actual reduction G_B is bounded constructible, since
its pullback is the assumed constructible reduction of K. Write J = j_! G.
The open tensor identity on a K-flat resolution gives the B-linear isomorphism
L_B J = j_!^B G_B: extension by zero preserves K-flatness since its tensor identity
and exactness preserve acyclicity. The proper torsion projection formula gives
(Rp_* J) tensor_A^L B = Rp_*(J tensor_A^L B). Its right side is bounded by proper
constructibility applied to the restriction of j_!^B G_B, so the left side, and
hence its B-linear version, are bounded as well. Apply scalarMate_restrict_eq_projection
to these bounded objects. The restriction of the canonical B-linear proper scalar
mate is the projection isomorphism, so conservativity of exact scalar restriction
makes that mate invertible. Compose with the open B-linear comparison. Transport
through the canonical compact-support site comparisons at A and B and the scalar
comparison on the target. Their unit/counit normalizations identify this composite
with precisely the displayed scalar-adjunction transpose using
sfCompactSupportRestriction. Consequently this particular map is invertible.
There is no finite Tor dimension assumption on the quotient map. The zero object,
empty schemes and m = n obey the same comparison identities. -/
theorem finiteCompactSupportScalarComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (K₀ : Type u) [Field K₀] (_hl : IsUnit (l : K₀))
    (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of K₀))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (K : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n))
    (hK : intrinsicFiniteTorsionConstructible l E n hn X K) :
    let := Padic.finite_coefficientExtensionRing l E n hn
    let := Padic.finite_coefficientExtensionRing l E m hm
    let φ := Ideal.Quotient.factor
      (S := Padic.coefficientExtensionIdeal l E n)
      (T := Padic.coefficientExtensionIdeal l E m) (Ideal.pow_le_pow_right hmn)
    let ρ := fun T : Scheme.{u} ↦
      (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} φ))
    intrinsicFiniteTorsionConstructible l E m hm X ((pbcDerivedExtend (ρ X)).obj K) →
    IsIso (((pbcDerivedScalarAdjunction (ρ Y)).homEquiv _ _).symm
      ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E n)).map
          ((pbcDerivedScalarAdjunction (ρ X)).unit.app K) ≫
        (sfCompactSupportRestriction c φ).hom.app ((pbcDerivedExtend (ρ X)).obj K))) := by
  classical
  let := Padic.finite_coefficientExtensionRing l E n hn
  let := Padic.finite_coefficientExtensionRing l E m hm
  let A := Padic.coefficientExtensionRing l E n
  let B := Padic.coefficientExtensionRing l E m
  let φ : A →+* B := Ideal.Quotient.factor
    (S := Padic.coefficientExtensionIdeal l E n)
    (T := Padic.coefficientExtensionIdeal l E m) (Ideal.pow_le_pow_right hmn)
  let ρ := FiniteCompactScalar.scalarRingMap φ
  dsimp only
  intro hred
  have : IsNoetherian Y := noetherianOfField K₀ Y
  have : IsNoetherian c.Z := noetherianCompactification c
  have hKo : (ObjectProperty.ι (Etale.DerivedCategory.isBoundedConstructible
      (ULift.{u + 1, u} A) X) ⋙
      ProEtale.finiteCoefficientIntrinsicDerivedComparison X A).essImage K := by
    apply ((finiteRing_constructibleDerived_origin X A).2.2.1 K).mpr
    obtain ⟨hs, hc⟩ := hK
    exact ⟨hc, (finite_homology_support_iff K).mp hs⟩
  obtain ⟨G₀, ⟨eK⟩⟩ := hKo
  have hGplus : DerivedCategory.TStructure.t.plus G₀.obj := by
    obtain ⟨a, b, hab, hv⟩ := G₀.property.2
    exact ⟨a, (DerivedCategory.isGE_iff _ a).mpr fun i hi ↦ hv i (Or.inl hi)⟩
  let G : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :=
    ⟨G₀.obj, hGplus⟩
  let LB := (Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1} φ) X).obj G.obj
  let eB : (ProEtale.finiteCoefficientIntrinsicDerivedComparison X B).obj LB ≅
      (pbcDerivedExtend (ρ X)).obj K :=
    (FiniteCompactScalar.siteScalarIso φ X).symm.app G.obj ≪≫
      (pbcDerivedExtend (ρ X)).mapIso eK
  obtain ⟨ared, bred, habred, hvred⟩ := (finite_homology_support_iff _).mp hred.1
  have hvB : ∀ i : ℤ, (i < ared ∨ bred < i) →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj LB) := by
    apply ((finiteRing_constructibleDerived_origin X B).2.2.2 LB ared bred).mpr
    intro i hi
    exact (hvred i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso eB)
  let GB : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) :=
    ⟨LB, ⟨ared, (DerivedCategory.isGE_iff _ ared).mpr
      fun i hi ↦ hvB i (Or.inl hi)⟩⟩
  let t := scalarMateTransformation
    (pbcDerivedScalarAdjunction (ρ X)) (pbcDerivedScalarAdjunction (ρ Y))
    (sfIntrinsicCompactSupport c A) (sfIntrinsicCompactSupport c B)
    (sfCompactSupportRestriction c φ).hom
  have ht : IsIso (t.app
      ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X A).obj G.obj)) := by
    change IsIso (((pbcDerivedScalarAdjunction (ρ Y)).homEquiv _ _).symm _)
    have heq := FiniteCompactScalar.intrinsicCompactScalarIsoOfOrigin_hom φ c G GB
      (Iso.refl _)
    exact heq ▸ (inferInstance : IsIso
      (FiniteCompactScalar.intrinsicCompactScalarIsoOfOrigin φ c G GB (Iso.refl _)).hom)
  have he : t.app K =
      (sfIntrinsicCompactSupport c A ⋙ pbcDerivedExtend (ρ Y)).map eK.inv ≫
        t.app ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X A).obj G.obj) ≫
        (pbcDerivedExtend (ρ X) ⋙ sfIntrinsicCompactSupport c B).map eK.hom := by
    rw [← t.naturality, ← Functor.map_comp_assoc, eK.inv_hom_id]
    change t.app K = (sfIntrinsicCompactSupport c A ⋙ pbcDerivedExtend (ρ Y)).map
      (𝟙 K) ≫ t.app K
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
  change IsIso (t.app K)
  rw [he]
  infer_instance

end AlgebraicGeometry.Scheme
