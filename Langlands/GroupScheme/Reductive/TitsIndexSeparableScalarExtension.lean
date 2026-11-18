import Langlands.GroupScheme.Reductive.StarActionScalarExtension
import Langlands.GroupScheme.Reductive.StarActionFiniteStageProof
import Langlands.GroupScheme.Reductive.TitsIndexExistenceProof
import Langlands.GroupScheme.SimplyConnected.SemisimpleFieldExtensionProof

/-! # Actual Tits-index Cartan and star comparison over separable intermediate fields -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.TitsIndexData

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G) (E : IntermediateField k (SeparableClosure k))

local instance closureAlgebra : Algebra E (SeparableClosure E) :=
  (separableClosure E (AlgebraicClosure E)).algebra

local instance scalarExtensionAffine :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k E)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom _)
  infer_instance

local instance scalarExtensionFiniteType :
    LocallyOfFiniteType ((GroupScheme.baseChange (algebraBaseMap k E)).obj G).X.hom := by
  change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom _)
  infer_instance

/-- A full actual Cartan-and-star comparison after extending the ground field
inside its separable closure. Distinguished vertices may change. -/
structure SeparableScalarExtension
    (e : SeparableClosure E ≃ₐ[E] SeparableClosure k) where
  index : TitsIndexData ((GroupScheme.baseChange (algebraBaseMap k E)).obj G)
  vertices : d.Vertex ≃ index.Vertex
  cartan_eq : ∀ a b, index.cartan (vertices a) (vertices b) = d.cartan a b
  star_eq : ∀ (τ : SeparableClosure E ≃ₐ[E] SeparableClosure E) a,
    vertices (d.star ((AlgEquiv.autCongr e τ).restrictScalars k) a) =
      index.star τ (vertices a)

/-- Every actual Tits index has an actual full Cartan-and-star comparison after
separable scalar extension, for each supplied comparison of separable closures. -/
theorem nonempty_separableScalarExtension
    (e : SeparableClosure E ≃ₐ[E] SeparableClosure k) :
    Nonempty (d.SeparableScalarExtension E e) := by
  let Q := GaloisPinningData.rootDatumScalarExtension (E := E) d.pinning
  let : Algebra (SeparableClosure E) (SeparableClosure k) := e.toRingHom.toAlgebra
  let : Algebra.IsSeparable E (SeparableClosure k) :=
    Algebra.isSeparable_tower_top_of_isSeparable k E (SeparableClosure k)
  have hc : algebraBaseMap (SeparableClosure E) (SeparableClosure k) ≫
      algebraBaseMap E (SeparableClosure E) = algebraBaseMap E (SeparableClosure k) := by
    simp only [algebraBaseMap, ← Spec.map_comp]
    congr 1
    ext x
    exact congrArg Subtype.val (e.commutes x)
  have hT : IsTorus Q.pinning.torus.toGrp :=
    ⟨SeparableClosure k, inferInstance, inferInstance, Q.pinning.isSplitTorus⟩
  have hsplit := GaloisPinningData.isSplitTorus_separableClosure Q.pinning.torus hT
  obtain ⟨q, ε, hεb, hεstar⟩ := StarActionFiniteStage.exists_stage Q.pinning hc hsplit
  let GE := (GroupScheme.baseChange (algebraBaseMap k E)).obj G
  have hGE : IsSemisimple GE := isSemisimpleFieldExtension k E G d.isSemisimple
  obtain ⟨dE⟩ := titsIndexExistence E GE hGE
  obtain ⟨g, φ, ζ, hg, hχ, hζb, hζstar⟩ :=
    StarActionIndependence.starActionIndependence E (SeparableClosure E) GE q dE.pinning
  change (∀ a, a ∈ q.base.support ↔ ε.indexEquiv a ∈ Q.pinning.base.support) at hεb
  change (∀ a, a ∈ q.base.support ↔ ζ.indexEquiv a ∈ dE.pinning.base.support) at hζb
  let f := ζ.comp (ε.symm.comp Q.rootEquiv)
  have hfb : ∀ a, a ∈ d.pinning.base.support ↔ f.indexEquiv a ∈ dE.pinning.base.support := by
    intro a
    change a ∈ d.pinning.base.support ↔
      ζ.indexEquiv (ε.indexEquiv.symm (Q.rootEquiv.indexEquiv a)) ∈ dE.pinning.base.support
    have hmid := hεb (ε.indexEquiv.symm (Q.rootEquiv.indexEquiv a))
    simp only [Equiv.apply_symm_apply] at hmid
    exact (Q.base_eq a).trans (hmid.symm.trans (hζb _))
  let v : d.Vertex ≃ dE.Vertex := f.indexEquiv.subtypeEquiv hfb
  refine ⟨⟨dE, v, fun a b => f.toHom.pairing, fun τ a => Subtype.ext ?_⟩⟩
  let ρ := AlgEquiv.autCongr e τ
  have hcompat : ∀ x, ρ (algebraMap (SeparableClosure E) (SeparableClosure k) x) =
      algebraMap (SeparableClosure E) (SeparableClosure k) (τ x) := by
    intro x
    change e (τ (e.symm (e x))) = e (τ x)
    rw [e.symm_apply_apply]
  have hQ := congrArg (fun z => z.indexEquiv a.val) (Q.star_eq ρ)
  have hε := congrArg (fun z => z.indexEquiv (ε.indexEquiv.symm (Q.rootEquiv.indexEquiv a.val)))
    (hεstar τ ρ hcompat)
  have hζ := congrArg (fun z => z.indexEquiv (ε.indexEquiv.symm (Q.rootEquiv.indexEquiv a.val)))
    (hζstar τ)
  change ζ.indexEquiv (ε.indexEquiv.symm
      (Q.rootEquiv.indexEquiv ((d.pinning.starAction (ρ.restrictScalars k)).val.indexEquiv a.val))) =
    (dE.pinning.starAction τ).val.indexEquiv
      (ζ.indexEquiv (ε.indexEquiv.symm (Q.rootEquiv.indexEquiv a.val)))
  change Q.rootEquiv.indexEquiv
      ((d.pinning.starAction (ρ.restrictScalars k)).val.indexEquiv a.val) =
    (Q.pinning.starAction ρ).val.indexEquiv (Q.rootEquiv.indexEquiv a.val) at hQ
  change ε.indexEquiv ((q.starAction τ).val.indexEquiv
      (ε.indexEquiv.symm (Q.rootEquiv.indexEquiv a.val))) =
    (Q.pinning.starAction ρ).val.indexEquiv
      (ε.indexEquiv (ε.indexEquiv.symm (Q.rootEquiv.indexEquiv a.val))) at hε
  have hε' := hε.trans (congrArg (Q.pinning.starAction ρ).val.indexEquiv
    (ε.indexEquiv.apply_symm_apply (Q.rootEquiv.indexEquiv a.val)))
  exact (congrArg (fun z => ζ.indexEquiv (ε.indexEquiv.symm z)) (hQ.trans hε'.symm)).trans
    ((congrArg ζ.indexEquiv (ε.indexEquiv.symm_apply_apply _)).trans hζ)

/-- Choose the actual Cartan-and-full-star comparison over a separable intermediate field. -/
def separableScalarExtension (e : SeparableClosure E ≃ₐ[E] SeparableClosure k) :
    d.SeparableScalarExtension E e :=
  Classical.choice (d.nonempty_separableScalarExtension E e)

end Langlands.GroupScheme.TitsIndexData
