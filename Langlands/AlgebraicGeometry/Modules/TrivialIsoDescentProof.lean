import Langlands.AlgebraicGeometry.Modules.TrivialIsoDescentStatement
import Langlands.AlgebraicGeometry.Descent.CompatibleUnitsProof
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Proof of descent of isomorphisms between trivial modules -/

universe u

open CategoryTheory AlgebraicGeometry Langlands.SchemeModule

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.Scheme.Modules

/-- The pullback of a trivialization on the base is compatible with the
canonical comparison and the structure-module identifications. -/
theorem baseTrivialization_compatible
    {U X Y : Scheme.{u}} (p : X ⟶ Y) (a b : U ⟶ X) (h : a ≫ p = b ≫ p)
    {M : Y.Modules} (τ : M ≅ structureModule Y) :
    (equalCompositeIso p a b h M).hom ≫
        (Scheme.Modules.pullback b).map
          (((Scheme.Modules.pullback p).mapIso τ ≪≫ pullbackUnitIso p).hom) ≫
        (pullbackUnitIso b).hom =
      (Scheme.Modules.pullback a).map
          (((Scheme.Modules.pullback p).mapIso τ ≪≫ pullbackUnitIso p).hom) ≫
        (pullbackUnitIso a).hom := by
  have he := congrArg Iso.hom (equalCompositeUnitAut_pullbackUnitIso p a b h)
  simp only [equalCompositeUnitAut_hom, Iso.refl_hom] at he
  have hu : (equalCompositeIso p a b h (structureModule Y)).hom ≫
      (Scheme.Modules.pullback b).map (pullbackUnitIso p).hom ≫
        (pullbackUnitIso b).hom =
      (Scheme.Modules.pullback a).map (pullbackUnitIso p).hom ≫
        (pullbackUnitIso a).hom := by
    apply (cancel_epi ((pullbackUnitIso a).inv ≫
      (Scheme.Modules.pullback a).map (pullbackUnitIso p).inv)).mp
    simpa only [structureModule, Category.assoc, Iso.inv_hom_id, Iso.inv_hom_id_assoc,
      Iso.map_inv_hom_id_assoc]
      using he
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [← equalCompositeIso_hom_naturality_assoc p a b h τ.hom, hu]

/-- A compatible isomorphism between pullbacks of two trivial modules has
compatible scalar after transporting by their base trivializations. -/
theorem scalar_compatible_of_base_trivializations
    {U X Y : Scheme.{u}} (p : X ⟶ Y) (a b : U ⟶ X) (h : a ≫ p = b ≫ p)
    {M N : Y.Modules} (τ : M ≅ structureModule Y) (σ : N ≅ structureModule Y)
    (e : (Scheme.Modules.pullback p).obj M ≅ (Scheme.Modules.pullback p).obj N)
    (he : (Scheme.Modules.pullback a).map e.hom ≫
        (equalCompositeIso p a b h N).hom =
      (equalCompositeIso p a b h M).hom ≫ (Scheme.Modules.pullback b).map e.hom) :
    Units.map a.appTop.hom.toMonoidHom
        (structureAutScalar
          (((Scheme.Modules.pullback p).mapIso τ ≪≫ pullbackUnitIso p).symm ≪≫ e ≪≫
            (Scheme.Modules.pullback p).mapIso σ ≪≫ pullbackUnitIso p)) =
      Units.map b.appTop.hom.toMonoidHom
        (structureAutScalar
          (((Scheme.Modules.pullback p).mapIso τ ≪≫ pullbackUnitIso p).symm ≪≫ e ≪≫
            (Scheme.Modules.pullback p).mapIso σ ≪≫ pullbackUnitIso p)) := by
  let α := (Scheme.Modules.pullback p).mapIso τ ≪≫ pullbackUnitIso p
  let β := (Scheme.Modules.pullback p).mapIso σ ≪≫ pullbackUnitIso p
  let δ := α.symm ≪≫ e ≪≫ β
  change Units.map a.appTop.hom.toMonoidHom (structureAutScalar δ) =
    Units.map b.appTop.hom.toMonoidHom (structureAutScalar δ)
  rw [← structureAutScalar_pullback a δ, ← structureAutScalar_pullback b δ]
  congr 1
  apply Iso.ext
  have hα := baseTrivialization_compatible p a b h τ
  have hβ := baseTrivialization_compatible p a b h σ
  change (equalCompositeIso p a b h M).hom ≫
    (Scheme.Modules.pullback b).map α.hom ≫ (pullbackUnitIso b).hom =
    (Scheme.Modules.pullback a).map α.hom ≫ (pullbackUnitIso a).hom at hα
  change (equalCompositeIso p a b h N).hom ≫
    (Scheme.Modules.pullback b).map β.hom ≫ (pullbackUnitIso b).hom =
    (Scheme.Modules.pullback a).map β.hom ≫ (pullbackUnitIso a).hom at hβ
  apply (cancel_epi ((Scheme.Modules.pullback a).map α.hom ≫
    (pullbackUnitIso a).hom)).mp
  simp only [structureAutPullback_hom, δ, Iso.trans_hom, Iso.symm_hom,
    Functor.map_comp, Category.assoc]
  simp only [Iso.hom_inv_id_assoc, Iso.map_hom_inv_id_assoc]
  rw [← hβ, ← Category.assoc, ← Category.assoc, he]
  simp only [Category.assoc]
  rw [← reassoc_of% hα]
  simp

/-- Units pull back injectively along an epimorphism of schemes. -/
theorem units_pullback_injective
    {X Y : Scheme.{u}} (p : X ⟶ Y) [Epi p] :
    Function.Injective (Units.map p.appTop.hom.toMonoidHom : Γ(Y, ⊤)ˣ → Γ(X, ⊤)ˣ) := by
  intro s t hst
  apply (Langlands.GroupScheme.Gm.unitsHomEquiv Y).symm.injective
  apply (cancel_epi p).mp
  apply (Langlands.GroupScheme.Gm.unitsHomEquiv X).injective
  simpa only [Langlands.GroupScheme.Gm.unitsHomEquiv_comp, Equiv.apply_symm_apply]
    using hst

/-- Normalization by base trivializations commutes with actual pullback. -/
theorem normalizeIso_pullback
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    {M N : Y.Modules} (τ : M ≅ structureModule Y) (σ : N ≅ structureModule Y)
    (e : M ≅ N) :
    (((Scheme.Modules.pullback p).mapIso τ ≪≫ pullbackUnitIso p).symm ≪≫
      (Scheme.Modules.pullback p).mapIso e ≪≫
      (Scheme.Modules.pullback p).mapIso σ ≪≫ pullbackUnitIso p) =
      structureAutPullback p (τ.symm ≪≫ e ≪≫ σ) := by
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, structureAutPullback_hom, Functor.map_comp, Category.assoc]

/-- Pullback distinguishes isomorphisms between two globally trivial modules. -/
theorem pullbackIso_injective_of_trivializations
    {X Y : Scheme.{u}} (p : X ⟶ Y) [Epi p]
    {M N : Y.Modules} (τ : M ≅ structureModule Y) (σ : N ≅ structureModule Y) :
    Function.Injective (fun e : M ≅ N ↦ (Scheme.Modules.pullback p).mapIso e) := by
  intro e e' he
  change (Scheme.Modules.pullback p).mapIso e =
    (Scheme.Modules.pullback p).mapIso e' at he
  have hnorm : structureAutPullback p (τ.symm ≪≫ e ≪≫ σ) =
      structureAutPullback p (τ.symm ≪≫ e' ≪≫ σ) := by
    rw [← normalizeIso_pullback p τ σ, ← normalizeIso_pullback p τ σ, he]
  have hs := congrArg structureAutScalar hnorm
  simp only [structureAutScalar_pullback] at hs
  have hd := structureAutScalar_injective (units_pullback_injective p hs)
  apply Iso.ext
  have hh := congrArg Iso.hom hd
  apply (cancel_epi τ.inv).mp
  apply (cancel_mono σ.hom).mp
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc] using hh

/-- A compatible isomorphism descends uniquely when the base modules are trivial. -/
theorem compatibleIsoDescent_of_trivializations
    {X Y : Scheme.{u}} (p : X ⟶ Y) [EffectiveEpi p]
    {M N : Y.Modules} (τ : M ≅ structureModule Y) (σ : N ≅ structureModule Y)
    (e : (Scheme.Modules.pullback p).obj M ≅ (Scheme.Modules.pullback p).obj N)
    (he : ∀ (U : Scheme.{u}) (a b : U ⟶ X) (h : a ≫ p = b ≫ p),
      (Scheme.Modules.pullback a).map e.hom ≫ (equalCompositeIso p a b h N).hom =
        (equalCompositeIso p a b h M).hom ≫ (Scheme.Modules.pullback b).map e.hom) :
    ∃! e₀ : M ≅ N, (Scheme.Modules.pullback p).mapIso e₀ = e := by
  let α := (Scheme.Modules.pullback p).mapIso τ ≪≫ pullbackUnitIso p
  let β := (Scheme.Modules.pullback p).mapIso σ ≪≫ pullbackUnitIso p
  let δ := α.symm ≪≫ e ≪≫ β
  obtain ⟨t, ht, _⟩ :=
    Langlands.Scheme.compatibleUnitsDescent_of_effectiveEpi p (structureAutScalar δ)
      (fun U a b h ↦ scalar_compatible_of_base_trivializations p a b h τ σ e
        (he U a b h))
  have hd : structureAutPullback p (structureAutOfUnit t) = δ := by
    apply structureAutScalar_injective
    rw [structureAutScalar_pullback, structureAutScalar_ofUnit]
    exact ht
  let e₀ := τ ≪≫ structureAutOfUnit t ≪≫ σ.symm
  have he₀ : (Scheme.Modules.pullback p).mapIso e₀ = e := by
    apply Iso.ext
    apply (cancel_epi α.inv).mp
    apply (cancel_mono β.hom).mp
    change (α.symm ≪≫ (Scheme.Modules.pullback p).mapIso e₀ ≪≫ β).hom = δ.hom
    have hn := normalizeIso_pullback p τ σ e₀
    change α.symm ≪≫ (Scheme.Modules.pullback p).mapIso e₀ ≪≫ β = _ at hn
    rw [hn]
    have hcancel : τ.symm ≪≫ e₀ ≪≫ σ = structureAutOfUnit t := by
      simp [e₀]
    rw [hcancel, hd]
  refine ⟨e₀, he₀, ?_⟩
  intro e' he'
  apply pullbackIso_injective_of_trivializations p τ σ
  exact he'.trans he₀.symm

/-- Compatible isomorphisms between trivial modules descend along fpqc morphisms. -/
theorem trivialIsoDescent : TrivialIsoDescentStatement.{u} := by
  intro X Y p hpqc hpflat hpsurj M N τ σ e he
  let : QuasiCompact p := hpqc
  let : Flat p := hpflat
  let : Surjective p := hpsurj
  exact compatibleIsoDescent_of_trivializations p τ σ e he

end Langlands.Scheme.Modules
