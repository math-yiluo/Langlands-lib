import Langlands.GroupScheme.HomImage
import Langlands.GroupScheme.SubgroupFunctor.QuotientNormality
import Langlands.GroupScheme.Reductive.UnipotentQuotient
import Langlands.GroupScheme.Reductive.AlgebraicallyClosedPseudoReductive
import Langlands.GroupScheme.ProductFactorInclusion
import Langlands.GroupScheme.ProductProperties
import Langlands.GroupScheme.GeometricConnectedness

/-! # Trivial unipotent radicals in finite products -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

namespace SubgroupFunctor

/-- Normality descends in a square whose ambient map has a section and whose
subgroup map is an fpqc quotient. -/
theorem isNormal_range_of_section_square
    {S : Scheme.{u}} {B G BQ Q : GroupScheme S}
    (i : B ⟶ G) (q : G ⟶ Q) (p : B ⟶ BQ) (j : BQ ⟶ Q)
    (s : Q ⟶ G) (hsection : s ≫ q = 𝟙 Q)
    [Flat p.hom.hom.left] [Surjective p.hom.hom.left]
    [QuasiCompact p.hom.hom.left] [Mono j.hom.hom]
    (hsquare : i ≫ q = p ≫ j) (hnormal : (range i).IsNormal) :
    (range j).IsNormal := by
  intro T g x _ hx
  obtain ⟨y, rfl⟩ := mem_range.mp hx
  apply mem_range_of_local_quotient_lift p j y
  intro W b y' hy
  have hs : i.hom.hom ≫ q.hom.hom = p.hom.hom ≫ j.hom.hom :=
    congrArg (fun f => f.hom.hom) hsquare
  have hsq : s.hom.hom ≫ q.hom.hom = 𝟙 Q.X :=
    congrArg (fun f => f.hom.hom) hsection
  have hnormal' := hnormal W (b ≫ g ≫ s.hom.hom) (y' ≫ i.hom.hom)
    (Subgroup.mem_top _) (mem_range.mpr ⟨y', rfl⟩)
  obtain ⟨z, hz⟩ := mem_range.mp hnormal'
  refine mem_range.mpr ⟨z ≫ p.hom.hom, ?_⟩
  calc
    (z ≫ p.hom.hom) ≫ j.hom.hom =
        (z ≫ i.hom.hom) ≫ q.hom.hom := by
      rw [Category.assoc, ← hs, ← Category.assoc]
    _ = ((b ≫ g ≫ s.hom.hom) * (y' ≫ i.hom.hom) *
        (b ≫ g ≫ s.hom.hom)⁻¹) ≫ q.hom.hom := by rw [hz]
    _ = b ≫ (g * (y ≫ j.hom.hom) * g⁻¹) := by
      simp only [MonObj.mul_comp, GrpObj.inv_comp, MonObj.comp_mul,
        GrpObj.comp_inv, Category.assoc]
      rw [hsq, Category.comp_id, hs,
        ← Category.assoc y' p.hom.hom j.hom.hom, ← hy]
      simp only [Category.assoc]

end SubgroupFunctor

private instance smoothGeometricallyConnected_comp :
    ((@Smooth ⊓ @GeometricallyConnected :
      MorphismProperty Scheme.{u})).IsStableUnderComposition where
  comp_mem f g hf hg := by
    let : Smooth f := hf.1
    let : Smooth g := hg.1
    let : GeometricallyConnected f := hf.2
    let : GeometricallyConnected g := hg.2
    exact ⟨inferInstance, GeometricallyConnected.comp f g⟩

private instance smoothGeometricallyConnected_id :
    ((@Smooth ⊓ @GeometricallyConnected :
      MorphismProperty Scheme.{u})).ContainsIdentities where
  id_mem X := by
    refine ⟨inferInstance, ⟨?_⟩⟩
    intro K _ x Y a b hp
    have : IsIso b := hp.isIso_snd_of_isIso
    exact b.homeomorph.connectedSpace_iff.mpr inferInstance

variable {k : Type u} [Field k] {I : Type u} [Finite I]
  (A : I → GroupScheme (Spec (CommRingCat.of k)))

/-- A finite product of affine groups locally of finite type with trivial
ground-field unipotent radicals again has trivial ground-field radical. -/
theorem HasTrivialUnipotentRadical.pi
    [∀ x, IsAffineHom (A x).X.hom] [∀ x, LocallyOfFiniteType (A x).X.hom]
    (hA : ∀ x, HasTrivialUnipotentRadical (A x)) :
    HasTrivialUnipotentRadical (pi A) := by
  classical
  have : IsAffineHom (GroupScheme.pi A).X.hom :=
    prop_pi_hom @IsAffineHom A (fun _ => inferInstance)
  intro H i hi hs hc hu hn
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsAffineHom H.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have : Smooth H.X.hom := hs
  have : ConnectedSpace H.X.left := hc
  apply le_antisymm _ (fun T => (bot_le : (⊥ : Subgroup (T ⟶ (GroupScheme.pi A).X)) ≤ _))
  intro T x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  change y ≫ i.hom.hom = 1
  apply (piPointsEquiv A T).injective
  funext a
  obtain ⟨D, inc, p, hinc, hp, hpf, hps, hpqc, _, hDs, hDc, _⟩ :=
    HomImage.exists_image (i ≫ Pi.π A a)
  have : IsClosedImmersion inc.hom.hom.left := hinc
  have : Mono inc.hom.hom := Over.mono_of_mono_left _
  have : Flat p.hom.hom.left := hpf
  have : Surjective p.hom.hom.left := hps
  have : QuasiCompact p.hom.hom.left := hpqc
  have hDn : (SubgroupFunctor.range inc).IsNormal :=
    SubgroupFunctor.isNormal_range_of_section_square i (Pi.π A a) p inc
      (piSingle A a) (piSingle_π_self A a) hp.symm hn
  have hbot := hA a D inc hinc hDs hDc (hu.of_flat_surjective p) hDn
  have hmem : (y ≫ i.hom.hom) ≫ (Pi.π A a).hom.hom ∈
      (SubgroupFunctor.range inc).carrier T := by
    refine SubgroupFunctor.mem_range.mpr ⟨y ≫ p.hom.hom, ?_⟩
    rw [Category.assoc, ← Grp.comp_hom_hom, hp, Grp.comp_hom_hom,
      ← Category.assoc]
  rw [hbot, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hmem
  simpa only [piPointsEquiv_apply, MonObj.one_comp] using hmem

/-- Finite products preserve pseudo-reductivity over an arbitrary field. -/
theorem isPseudoReductive_pi (hA : ∀ x, IsPseudoReductive (A x)) :
    IsPseudoReductive (pi A) := by
  let : ∀ x, Smooth (A x).X.hom := fun x => (hA x).smooth
  let : ∀ x, IsAffineHom (A x).X.hom := fun x => (hA x).isAffineHom
  let : ∀ x, ConnectedSpace (A x).X.left := fun x => (hA x).connectedSpace
  have hg : Smooth (pi A).X.hom ∧ GeometricallyConnected (pi A).X.hom := by
    apply prop_pi_hom (@Smooth ⊓ @GeometricallyConnected) A
    intro x
    exact ⟨inferInstance, (A x).geometricallyConnected_of_connected⟩
  let : GeometricallyConnected (pi A).X.hom := hg.2
  refine ⟨hg.1, prop_pi_hom @IsAffineHom A (fun _ => inferInstance), ?_, ?_⟩
  · exact GeometricallyConnected.connectedSpace_of_subsingleton (f := (pi A).X.hom)
  · exact HasTrivialUnipotentRadical.pi A (fun x => (hA x).hasTrivialUnipotentRadical)

/-- Over an algebraically closed field, finite products of connected reductive
groups are connected reductive. -/
theorem isConnectedReductive_pi_of_isAlgClosed [IsAlgClosed k]
    (hA : ∀ x, IsConnectedReductive (A x)) : IsConnectedReductive (pi A) :=
  (isPseudoReductive_pi A (fun x => (hA x).isPseudoReductive)).isConnectedReductive_of_isAlgClosed

end Langlands.GroupScheme
