import Langlands.GroupScheme.Reductive.StarActionIndependenceProof
import Langlands.AbelianScheme.Tate.BaseChangeCoherence
import Langlands.GroupScheme.Torus.StrictHenselianMaximalReduction

/-! # Galois actions on characters along a tower of base changes -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace StarActionFiniteStage

/-! ### Points of base-changed characters -/

section Points

variable {S S' : Scheme.{u}} (b : S' ⟶ S) (T : CommGroupScheme S)

/-- A base-changed character evaluates the original character at the same point. -/
theorem characterLattice_baseChange_points (ψ : characterLattice T) (U : Over S')
    (z : U ⟶ ((CommGroupScheme.baseChange b).obj T).X) :
    Gm.pointsEquiv S' U
        (z ≫ (CommGroupScheme.groupHom (characterLattice.baseChange b T ψ)).hom.hom) =
      Gm.pointsEquiv S ((Over.map b).obj U)
        (baseChangePointsEquiv b T.toGrp U z ≫ (CommGroupScheme.groupHom ψ).hom.hom) :=
  rationalCharacters.characterEval_baseChange b (G := T.toGrp)
    (Additive.ofMul (CommGroupScheme.groupHom ψ)) U z

end Points

/-! ### The tower isomorphism -/

section Tower

variable {B SL SK : Scheme.{u}} (bL : SL ⟶ B) (j : SK ⟶ SL) (T : CommGroupScheme B)

/-- Pulling back along `j ≫ bL` is pulling back along `bL` and then along `j`. -/
def towerIso : (CommGroupScheme.baseChange (j ≫ bL)).obj T ≅
    (CommGroupScheme.baseChange j).obj ((CommGroupScheme.baseChange bL).obj T) :=
  CommGroupScheme.isoOfGroupIso (baseChangeCompIso bL j T.toGrp)

theorem groupHom_towerIso_hom :
    CommGroupScheme.groupHom (towerIso bL j T).hom =
      (baseChangeCompIso bL j T.toGrp).hom := rfl

/-- Changing the structure map of a test scheme along `aK` and then `j`, or along `j` and then
`aL`, gives the same scheme over `SL` when `j ≫ aL = aK ≫ j`. -/
def towerTestHom (aL : SL ⟶ SL) (aK : SK ⟶ SK) (hcomm : j ≫ aL = aK ≫ j) (U : Over SK) :
    (Over.map j).obj ((Over.map aK).obj U) ⟶ (Over.map aL).obj ((Over.map j).obj U) :=
  Over.homMk (𝟙 U.left) (by
    change 𝟙 U.left ≫ (U.hom ≫ j) ≫ aL = (U.hom ≫ aK) ≫ j
    rw [Category.id_comp, Category.assoc, hcomm, Category.assoc])

@[simp] theorem towerTestHom_left (aL : SL ⟶ SL) (aK : SK ⟶ SK) (hcomm : j ≫ aL = aK ≫ j)
    (U : Over SK) : (towerTestHom j aL aK hcomm U).left = 𝟙 U.left := rfl

/-- The point of `G_L` obtained by transporting a point of `G_K` first along `aK` and then down
to `L` agrees with the point obtained by going down to `L` first and transporting along
`aL`. -/
theorem towerTestHom_comp_descentPoint (G : Grp (Over B)) (aL : SL ⟶ SL) (haL : aL ≫ bL = bL)
    (aK : SK ⟶ SK) (haK : aK ≫ j ≫ bL = j ≫ bL) (hcomm : j ≫ aL = aK ≫ j) (U : Over SK)
    (y : U ⟶ ((Over.pullback (j ≫ bL)).mapGrp.obj G).X) :
    towerTestHom j aL aK hcomm U ≫
        descentPoint bL aL haL G ((Over.map j).obj U)
          (baseChangePointsEquiv j ((Over.pullback bL).mapGrp.obj G) U
            (y ≫ (baseChangeCompIso bL j G).hom.hom.hom)) =
      baseChangePointsEquiv j ((Over.pullback bL).mapGrp.obj G) ((Over.map aK).obj U)
        (descentPoint (j ≫ bL) aK haK G U y ≫ (baseChangeCompIso bL j G).hom.hom.hom) := by
  apply (baseChangePointsEquiv bL G _).injective
  rw [baseChangePointsEquiv_naturality, baseChangePointsEquiv_descentPoint,
    baseChangePointsEquiv_base_comp, baseChangePointsEquiv_base_comp]
  have hinv : ∀ {V : Over SK} (z : V ⟶ ((Over.pullback (j ≫ bL)).mapGrp.obj G).X),
      (z ≫ (baseChangeCompIso bL j G).hom.hom.hom) ≫
        (baseChangeCompIso bL j G).inv.hom.hom = z := by
    intro V z
    rw [Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id]
    exact Category.comp_id z
  rw [hinv, hinv, baseChangePointsEquiv_descentPoint]
  apply Over.OverMorphism.ext
  simp [descentTestIso, Over.mapComp]

/-- The lattice map `X^*(T_L) → X^*(T_K)`: base change along `j`, then the tower isomorphism. -/
def towerCharacter (χ : characterLattice ((CommGroupScheme.baseChange bL).obj T)) :
    characterLattice ((CommGroupScheme.baseChange (j ≫ bL)).obj T) :=
  (towerIso bL j T).hom ≫ characterLattice.baseChange j _ χ

/-- **Tower compatibility.** The tower lattice map intertwines transport along `aL` on
`X^*(T_L)` with transport along `aK` on `X^*(T_K)` whenever `j ≫ aL = aK ≫ j`. -/
theorem towerCharacter_transport (aL : SL ⟶ SL) (haL : aL ≫ bL = bL) (aK : SK ⟶ SK)
    (haK : aK ≫ j ≫ bL = j ≫ bL) (hcomm : j ≫ aL = aK ≫ j)
    (χ : characterLattice ((CommGroupScheme.baseChange bL).obj T)) :
    towerCharacter bL j T (characterLattice.transport bL aL haL T χ) =
      characterLattice.transport (j ≫ bL) aK haK T (towerCharacter bL j T χ) := by
  apply characterLattice.ext_points
  intro U y
  let yL : (Over.map j).obj U ⟶ ((Over.pullback bL).mapGrp.obj T.toGrp).X :=
    baseChangePointsEquiv j ((Over.pullback bL).mapGrp.obj T.toGrp) U
      (y ≫ (baseChangeCompIso bL j T.toGrp).hom.hom.hom)
  have h1 : Gm.pointsEquiv SK U (y ≫ (CommGroupScheme.groupHom
        (towerCharacter bL j T (characterLattice.transport bL aL haL T χ))).hom.hom) =
      Gm.pointsEquiv SL ((Over.map aL).obj ((Over.map j).obj U))
        (descentPoint bL aL haL T.toGrp ((Over.map j).obj U) yL ≫
          (CommGroupScheme.groupHom χ).hom.hom) :=
    ((congrArg (Gm.pointsEquiv SK U) (comp_groupHom_comp y (towerIso bL j T).hom
      (characterLattice.baseChange j _ (characterLattice.transport bL aL haL T χ)))).trans
      (characterLattice_baseChange_points j ((CommGroupScheme.baseChange bL).obj T)
        (characterLattice.transport bL aL haL T χ) U
        (y ≫ (CommGroupScheme.groupHom (towerIso bL j T).hom).hom.hom))).trans
      (characterLattice.transport_points bL aL haL T χ ((Over.map j).obj U) yL)
  have h2 : Gm.pointsEquiv SK U (y ≫ (CommGroupScheme.groupHom
        (characterLattice.transport (j ≫ bL) aK haK T (towerCharacter bL j T χ))).hom.hom) =
      Gm.pointsEquiv SL ((Over.map j).obj ((Over.map aK).obj U))
        (towerTestHom j aL aK hcomm U ≫
          descentPoint bL aL haL T.toGrp ((Over.map j).obj U) yL ≫
            (CommGroupScheme.groupHom χ).hom.hom) := by
    refine ((characterLattice.transport_points (j ≫ bL) aK haK T (towerCharacter bL j T χ) U
      y).trans ?_)
    refine ((congrArg (Gm.pointsEquiv SK ((Over.map aK).obj U))
      (comp_groupHom_comp (descentPoint (j ≫ bL) aK haK T.toGrp U y) (towerIso bL j T).hom
        (characterLattice.baseChange j _ χ))).trans ?_)
    refine ((characterLattice_baseChange_points j ((CommGroupScheme.baseChange bL).obj T) χ
      ((Over.map aK).obj U) (descentPoint (j ≫ bL) aK haK T.toGrp U y ≫
        (CommGroupScheme.groupHom (towerIso bL j T).hom).hom.hom)).trans ?_)
    have h := towerTestHom_comp_descentPoint bL j T.toGrp aL haL aK haK hcomm U y
    refine (congrArg (fun z => Gm.pointsEquiv SL ((Over.map j).obj ((Over.map aK).obj U))
      (z ≫ (CommGroupScheme.groupHom χ).hom.hom)) h.symm).trans ?_
    exact congrArg (Gm.pointsEquiv SL ((Over.map j).obj ((Over.map aK).obj U)))
      (Category.assoc _ _ _)
  refine (h1.trans ?_).trans h2.symm
  refine Eq.trans ?_ (Gm.pointsEquiv_naturality SL (towerTestHom j aL aK hcomm U) _).symm
  change _ = Units.map (𝟙 U.left : U.left ⟶ U.left).appTop.hom.toMonoidHom _
  simp

/-! ### Along an equality of base maps -/

variable (bK : SK ⟶ B) (hc : j ≫ bL = bK)

/-- The tower isomorphism, along a base map equal to `j ≫ bL`. -/
def towerIsoOf : (CommGroupScheme.baseChange bK).obj T ≅
    (CommGroupScheme.baseChange j).obj ((CommGroupScheme.baseChange bL).obj T) :=
  eqToIso (congrArg (fun c => (CommGroupScheme.baseChange c).obj T) hc.symm) ≪≫
    towerIso bL j T

/-- The group tower isomorphism, along a base map equal to `j ≫ bL`. -/
def groupTowerIsoOf (G : GroupScheme B) : (GroupScheme.baseChange bK).obj G ≅
    (GroupScheme.baseChange j).obj ((GroupScheme.baseChange bL).obj G) :=
  eqToIso (congrArg (fun c => (GroupScheme.baseChange c).obj G) hc.symm) ≪≫
    GroupScheme.baseChangeCompIso bL j G

/-- The tower isomorphisms of a torus and of an ambient group are compatible with the
base changes of the inclusion. -/
theorem towerIsoOf_square {G : GroupScheme B} (i : T.toGrp ⟶ G) :
    (GroupScheme.baseChange bK).map i ≫ (groupTowerIsoOf bL j bK hc G).hom =
      CommGroupScheme.groupHom (towerIsoOf bL j T bK hc).hom ≫
        (GroupScheme.baseChange j).map ((GroupScheme.baseChange bL).map i) := by
  subst hc
  simp only [groupTowerIsoOf, towerIsoOf, eqToIso_refl, Iso.refl_trans]
  exact baseChangeCompIso_hom_naturality bL j i

/-- After base change along `bK = j ≫ bL`, a homomorphism of group schemes over `B` becomes
its two-step base change, up to the group tower isomorphisms. -/
theorem baseChange_map_eq_groupTowerIsoOf {H G : GroupScheme B} (i : H ⟶ G) :
    (GroupScheme.baseChange j).map ((GroupScheme.baseChange bL).map i) =
      (groupTowerIsoOf bL j bK hc H).inv ≫ (GroupScheme.baseChange bK).map i ≫
        (groupTowerIsoOf bL j bK hc G).hom := by
  subst hc
  simp only [groupTowerIsoOf, eqToIso_refl, Iso.refl_trans]
  rw [baseChangeCompIso_hom_naturality bL j i, Iso.inv_hom_id_assoc]

/-- The tower lattice map, along a base map equal to `j ≫ bL`. -/
def towerCharacterOf (χ : characterLattice ((CommGroupScheme.baseChange bL).obj T)) :
    characterLattice ((CommGroupScheme.baseChange bK).obj T) :=
  (towerIsoOf bL j T bK hc).hom ≫ characterLattice.baseChange j _ χ

/-- Tower compatibility, along a base map equal to `j ≫ bL`. -/
theorem towerCharacterOf_transport (aL : SL ⟶ SL) (haL : aL ≫ bL = bL) (aK : SK ⟶ SK)
    (haK : aK ≫ bK = bK) (hcomm : j ≫ aL = aK ≫ j)
    (χ : characterLattice ((CommGroupScheme.baseChange bL).obj T)) :
    towerCharacterOf bL j T bK hc (characterLattice.transport bL aL haL T χ) =
      characterLattice.transport bK aK haK T (towerCharacterOf bL j T bK hc χ) := by
  subst hc
  have h := towerCharacter_transport bL j T aL haL aK haK hcomm χ
  simpa only [towerCharacterOf, towerCharacter, towerIsoOf, eqToIso_refl, Iso.refl_trans] using h

end Tower

/-! ### Based projections for pinnings over two fields -/

section Pinnings

open StarActionIndependence

variable {k k' : Type u} [Field k] [Field k']
  {G : GroupScheme (Spec (CommRingCat.of k))} {H : GroupScheme (Spec (CommRingCat.of k'))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  (p : SplitPinning G) (q : SplitPinning H)

/-- Conjugation by an equivalence preserving the chosen bases preserves based
automorphisms. The two pinnings may live over different fields. -/
theorem conjAut_mem_basedRootDatumAut (e : RootPairing.Equiv p.rootDatum q.rootDatum)
    (he : ∀ a, a ∈ p.base.support ↔ e.indexEquiv a ∈ q.base.support)
    {x : p.rootDatum.Aut} (hx : x ∈ p.basedRootDatumAut) :
    conjAut e x ∈ q.basedRootDatumAut := by
  intro a
  obtain ⟨a, rfl⟩ := e.indexEquiv.surjective a
  rw [conjAut_indexEquiv, Equiv.symm_apply_apply, ← he, ← he]
  exact hx a

/-- The based projections of an automorphism and of any element of the Weyl coset of
its conjugate correspond under a base-preserving equivalence. The two pinnings may live
over different fields. -/
theorem comp_basedRootDatumProjection (e : RootPairing.Equiv p.rootDatum q.rootDatum)
    (he : ∀ a, a ∈ p.base.support ↔ e.indexEquiv a ∈ q.base.support)
    (x : p.rootDatum.Aut) (x' : q.rootDatum.Aut)
    (hx : x' * (conjAut e x)⁻¹ ∈ q.rootDatum.weylGroup) :
    e.comp (p.basedRootDatumProjection x).val =
      (q.basedRootDatumProjection x').val.comp e := by
  have hθ := p.basedRootDatumProjection_correction x
  have hb : conjAut e (p.basedRootDatumProjection x).val ∈ q.basedRootDatumAut :=
    conjAut_mem_basedRootDatumAut p q e he (p.basedRootDatumProjection x).property
  have hproj : q.basedRootDatumProjection x' = ⟨_, hb⟩ := by
    apply q.basedRootDatum_representative_unique x' _ _
      (q.basedRootDatumProjection_correction x')
    change conjAut e (p.basedRootDatumProjection x).val * x'⁻¹ ∈ q.rootDatum.weylGroup
    have heq : conjAut e (p.basedRootDatumProjection x).val * x'⁻¹ =
        conjAut e ((p.basedRootDatumProjection x).val * x⁻¹) *
          (x' * (conjAut e x)⁻¹)⁻¹ := by
      rw [map_mul, map_inv]
      group
    rw [heq]
    exact mul_mem (conjAut_mem_weylGroup e hθ) (inv_mem hx)
  rw [hproj, comp_eq_conjAut_comp]

end Pinnings

end StarActionFiniteStage

end Langlands.GroupScheme
