import Langlands.GroupScheme.Torus.ExponentHomomorphisms

/-! # Descent of automorphisms of a supplied split torus -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme
namespace splitTorus

variable (k K : Type u) [Field k] [Field K]
  (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
  (I : Type u) [Fintype I] [DecidableEq I]

/-- Extend the integral-coordinate automorphism in commutative notation. -/
def fieldCommAutomorphismExtension
    (c : commGroupScheme (Spec (CommRingCat.of K)) I ≅
      commGroupScheme (Spec (CommRingCat.of K)) I) :
    commGroupScheme (Spec (CommRingCat.of k)) I ≅
      commGroupScheme (Spec (CommRingCat.of k)) I :=
  CommGroupScheme.isoOfGroupIso
    (fieldAutomorphismExtension K I (Spec (CommRingCat.of k))
      { hom := CommGroupScheme.groupHom c.hom
        inv := CommGroupScheme.groupHom c.inv
        hom_inv_id := congrArg CommGroupScheme.groupHom c.hom_inv_id
        inv_hom_id := congrArg CommGroupScheme.groupHom c.inv_hom_id })

/-- The extended commutative automorphism recovers the specified field map. -/
theorem fieldCommAutomorphismExtension_baseChange
    (c : commGroupScheme (Spec (CommRingCat.of K)) I ≅
      commGroupScheme (Spec (CommRingCat.of K)) I) :
    (commBaseChangeIso b I).inv ≫
      (CommGroupScheme.baseChange b).map (fieldCommAutomorphismExtension k K I c).hom ≫
        (commBaseChangeIso b I).hom = c.hom := by
  exact congrArg Additive.ofMul
    (fieldAutomorphismExtension_baseChange K I (Spec (CommRingCat.of k))
      { hom := CommGroupScheme.groupHom c.hom
        inv := CommGroupScheme.groupHom c.inv
        hom_inv_id := congrArg CommGroupScheme.groupHom c.hom_inv_id
        inv_hom_id := congrArg CommGroupScheme.groupHom c.inv_hom_id } b)

end splitTorus

namespace IsSplitTorus

variable {k K : Type u} [Field k] [Field K]
  (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Every automorphism of the base change of a supplied split torus descends. -/
theorem automorphism_baseChange_surjective (hT : IsSplitTorus T.toGrp) :
    Function.Surjective
      (fun σ : T ≅ T => (CommGroupScheme.baseChange b).mapIso σ) := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let := hI
  let := Fintype.ofFinite I
  let eC : T ≅ splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I :=
    CommGroupScheme.isoOfGroupIso e
  let B := CommGroupScheme.baseChange b
  let d := splitTorus.commBaseChangeIso b I
  let q := B.mapIso eC ≪≫ d
  intro σ'
  let c := q.symm ≪≫ σ' ≪≫ q
  let c₀ := splitTorus.fieldCommAutomorphismExtension k K I c
  refine ⟨eC ≪≫ c₀ ≪≫ eC.symm, ?_⟩
  apply Iso.ext
  change B.map (eC.hom ≫ c₀.hom ≫ eC.inv) = σ'.hom
  have hc : d.inv ≫ B.map c₀.hom ≫ d.hom = c.hom :=
    splitTorus.fieldCommAutomorphismExtension_baseChange k K b I c
  have hc' : B.map c₀.hom = d.hom ≫ c.hom ≫ d.inv := by
    rw [← hc]
    simp only [Iso.hom_inv_id_assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [Functor.map_comp, Functor.map_comp, hc']
  dsimp only [c, q, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    Functor.mapIso_hom, Functor.mapIso_inv]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp_assoc,
    Iso.hom_inv_id, Category.comp_id]
  rw [B.map_id, Category.id_comp, ← B.map_comp, eC.hom_inv_id,
    B.map_id, Category.comp_id]

/-- A chosen ground-field automorphism inducing a supplied extension-field one. -/
def descendedAutomorphism (hT : IsSplitTorus T.toGrp)
    (σ' : (CommGroupScheme.baseChange b).obj T ≅ (CommGroupScheme.baseChange b).obj T) :
    T ≅ T :=
  (hT.automorphism_baseChange_surjective b σ').choose

/-- Base change of the chosen descent is the exact supplied automorphism. -/
theorem descendedAutomorphism_spec (hT : IsSplitTorus T.toGrp)
    (σ' : (CommGroupScheme.baseChange b).obj T ≅ (CommGroupScheme.baseChange b).obj T) :
    (CommGroupScheme.baseChange b).mapIso (hT.descendedAutomorphism b σ') = σ' :=
  (hT.automorphism_baseChange_surjective b σ').choose_spec

end IsSplitTorus
end Langlands.GroupScheme
