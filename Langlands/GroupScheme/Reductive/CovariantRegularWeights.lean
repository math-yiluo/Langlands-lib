import Langlands.GroupScheme.Reductive.SplitBorelCellAction
import Langlands.GroupScheme.Reductive.CovariantCellRestriction
import Langlands.GroupScheme.MatrixRepresentation.SplitTorusCharacterDecomposition
import Langlands.GroupScheme.Rational.GeneralLinearCharacterAdapters

/-! # Torus weights of actual covariant regular representations -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Module
open scoped Matrix CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000

namespace Langlands.GroupScheme

namespace MatrixRepresentation

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {n : Type} [Fintype n] [DecidableEq n]

/-- Character vectors satisfy the eigenvector equation on every scheme test. -/
theorem characterSpace_points {ρ : MatrixRepresentation G n}
    {χ : rationalCharacters G} {v : n → k} (hv : v ∈ ρ.characterSpace χ)
    (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X) :
    (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *ᵥ
        (fun r => scalarMap T (v r)) =
      (characterEval χ T x : Γ(T.left, ⊤)) •
        (fun r => scalarMap T (v r)) := by
  let A := CharacterUnits.Coord G
  let U := (algSpec (CommRingCat.of k)).obj (op A)
  let z := CharacterUnits.universalPoint G
  let e := Corepresented.affineSectionsAlgEquiv A
  have hz : (ρ.pointMatrix U z : Matrix n n Γ(U.left, ⊤)) *ᵥ
        (fun r => scalarMap U (v r)) =
      (characterEval χ U z : Γ(U.left, ⊤)) •
        (fun r => scalarMap U (v r)) := by
    rw [pointMatrix_eq_affineMatrix]
    have hc : (characterEval χ U z : Γ(U.left, ⊤)) =
        e.symm (Gm.affineUnitsEquiv (CommRingCat.of k) A
          (z ≫ χ.toMul.hom.hom) : A) :=
      congrArg Units.val (GeneralLinear.gm_pointsEquiv_eq_affinePointsEquiv A
        (z ≫ χ.toMul.hom.hom))
    rw [hc]
    funext r
    have hs (c : k) : scalarMap U c = e.symm (algebraMap k A c) :=
      UnipotentMatrixCriterion.scalarMap_affine A c
    simp only [hs]
    change (((ρ.affineMatrix A z : Matrix n n A).map e.symm.toRingHom) *ᵥ
      (fun r => e.symm (algebraMap k A (v r)))) r = _
    have h := congrArg (fun w : n → A => e.symm (w r))
      (characterSpace_affine hv A z)
    calc
      _ = e.symm (((ρ.affineMatrix A z : Matrix n n A) *ᵥ
          (fun r => algebraMap k A (v r))) r) :=
        (e.symm.toRingHom.map_mulVec
          (ρ.affineMatrix A z : Matrix n n A)
          (fun r => algebraMap k A (v r)) r).symm
      _ = _ := by simpa only [Pi.smul_apply, smul_eq_mul, map_mul] using h
  let a : T ⟶ U := x ≫ (Lie.coordinateIso G).inv
  have ha : a ≫ z = x := by
    simp [a, z, CharacterUnits.universalPoint_eq]
  have hmat := ρ.pointMatrix_naturality a z
  rw [ha] at hmat
  rw [hmat]
  funext r
  have h := congrArg (fun w => a.left.appTop.hom (w r)) hz
  rw [a.left.appTop.hom.map_mulVec] at h
  have hc := congrArg Units.val (characterEval_naturality χ a z)
  rw [ha] at hc
  change (((ρ.pointMatrix U z : Matrix n n Γ(U.left, ⊤)).map
    a.left.appTop.hom) *ᵥ (fun r => scalarMap T (v r))) r = _
  have hs (c : k) : a.left.appTop.hom (scalarMap U c) = scalarMap T c :=
    scalarMap_naturality a c
  have hc' : a.left.appTop.hom (characterEval χ U z : Γ(U.left, ⊤)) =
      (characterEval χ T x : Γ(T.left, ⊤)) := hc.symm
  simpa only [Pi.smul_apply, smul_eq_mul, map_mul, Function.comp_def, hs, hc'] using h

end MatrixRepresentation

/-- Comparison of the two actual character evaluation conventions on affine tests. -/
theorem characterEval_eq_section_characterValue {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (χ : characterLattice S) (A : Type u) [CommRing A] [Algebra k A]
    (s : Lie.AffinePoints S.toGrp A) :
    (characterEval ((rationalCharacters.equivCharacterLattice S).symm χ)
      ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) A))) s :
        Γ(((algSpec (CommRingCat.of k)).obj
          (op (CommAlgCat.of (CommRingCat.of k) A))).left, ⊤)) =
      (Corepresented.affineSectionsAlgEquiv (CommAlgCat.of (CommRingCat.of k) A)).symm
        (Lie.characterValue χ s : A) := by
  exact congrArg Units.val
    (GeneralLinear.gm_pointsEquiv_eq_affinePointsEquiv (CommAlgCat.of (CommRingCat.of k) A)
      (s ≫ (CommGroupScheme.groupHom χ).hom.hom))

namespace AffineCoordinates

variable {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]

local instance covariantRegularWeightsIsAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- Comparison of the two chosen affine coordinate presentations of the same group. -/
def lieCoordinateEquiv : algebra G ≃ₐ[k] CharacterUnits.Coord G :=
  CommAlgCat.algEquivOfIso
    (algSpec.fullyFaithful.preimageIso
      ((Lie.coordinateIso G) ≪≫
        (asIso (groupSchemeIso G).hom.hom.hom).symm)).unop

/-- The coordinate comparison classifies exactly the supplied affine point. -/
theorem algPoint_lieCoordinateEquiv {A : CommAlgCat (CommRingCat.of k)}
    (x : G.affinePoints A) :
    algPoint G (CommAlgCat.ofHom
      ((Lie.pointCoordinates G x).comp (lieCoordinateEquiv G).toAlgHom)) = x := by
  change (algSpec (CommRingCat.of k)).map
    (CommAlgCat.ofHom
      ((Lie.pointCoordinates G x).comp (lieCoordinateEquiv G).toAlgHom)).op ≫
        (groupSchemeIso G).hom.hom.hom = x
  have he : (algSpec (CommRingCat.of k)).map
      (CommAlgCat.ofHom (lieCoordinateEquiv G).toAlgHom).op =
        (Lie.coordinateIso G).hom ≫ (groupSchemeIso G).inv.hom.hom := by
    change (algSpec (CommRingCat.of k)).map
      (algSpec.fullyFaithful.preimageIso
        ((Lie.coordinateIso G) ≪≫
          (asIso (groupSchemeIso G).hom.hom.hom).symm)).hom = _
    rw [Functor.FullyFaithful.preimageIso_hom, algSpec.fullyFaithful.map_preimage]
    apply (cancel_mono (groupSchemeIso G).hom.hom.hom).1
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
      ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
    change (Lie.coordinateIso G).hom ≫
      ((asIso (groupSchemeIso G).hom.hom.hom).inv ≫
        (asIso (groupSchemeIso G).hom.hom.hom).hom) = _
    rw [Iso.inv_hom_id, Category.comp_id]
  rw [show (CommAlgCat.ofHom
      ((Lie.pointCoordinates G x).comp (lieCoordinateEquiv G).toAlgHom)).op =
        (CommAlgCat.ofHom (Lie.pointCoordinates G x)).op ≫
          (CommAlgCat.ofHom (lieCoordinateEquiv G).toAlgHom).op from rfl,
    Functor.map_comp, he]
  simp only [Category.assoc, ← Grp.comp_hom_hom,
    Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
  change (algSpec (CommRingCat.of k)).map
    (algSpec.fullyFaithful.preimage (x ≫ (Lie.coordinateIso G).inv)) ≫
      (Lie.coordinateIso G).hom = x
  rw [algSpec.fullyFaithful.map_preimage, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- Evaluation in either affine presentation agrees under the canonical section map. -/
theorem pointAlgebraHom_lieCoordinateEquiv {A : CommAlgCat (CommRingCat.of k)}
    (x : G.affinePoints A) (f : algebra G) :
    pointAlgebraHom G _ x f =
      (Corepresented.affineSectionsAlgEquiv A).symm
        (Lie.pointCoordinates G x (lieCoordinateEquiv G f)) := by
  have h := pointAlgebraHom_algPoint G
    (CommAlgCat.ofHom
      ((Lie.pointCoordinates G x).comp (lieCoordinateEquiv G).toAlgHom))
  rw [algPoint_lieCoordinateEquiv] at h
  exact congrArg (fun φ => φ f) h

end AffineCoordinates

namespace Chevalley

open AffineCoordinates AffineLinearEmbedding MatrixRepresentation

variable {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

variable (V : Submodule k (algebra G)) {d : ℕ} (b : Basis (Fin d) k V)
    (hV : letI := (bialgebra (corepresentation G)).toCoalgebra
      ∀ (ψ : Module.Dual k (algebra G)) (w : algebra G),
        w ∈ V → rightAct ψ w ∈ V)
    {D : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom D.X.hom]
    (j : D ⟶ G) {χ : rationalCharacters D} {v : Fin d → k}

/-- An actual character vector gives a right-character regular function. -/
theorem pointAlgebraHom_affineRegularCoordinateMap_mul_of_character
    (hv : v ∈ ((affineRegularRepresentation G V b hV).restrict j).characterSpace χ)
    (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ D.X) (g : T ⟶ G.X) :
    pointAlgebraHom G T (g * (s ≫ j.hom.hom))
        (affineRegularCoordinateMap G V b v) =
      (show ((algΓ (CommRingCat.of k)).obj T).unop from
        (characterEval χ T s : Γ(T.left, ⊤))) *
        pointAlgebraHom G T g (affineRegularCoordinateMap G V b v) := by
  rw [pointAlgebraHom_affineRegularCoordinateMap_mul G V b hV]
  have he := MatrixRepresentation.characterSpace_points hv T s
  rw [pointMatrix_restrict] at he
  let M : Matrix (Fin d) (Fin d) ((algΓ (CommRingCat.of k)).obj T).unop :=
    ((affineRegularRepresentation G V b hV).pointMatrix T (s ≫ j.hom.hom) :
      Matrix (Fin d) (Fin d) Γ(T.left, ⊤))
  let c : ((algΓ (CommRingCat.of k)).obj T).unop :=
    (characterEval χ T s : Γ(T.left, ⊤))
  have he' : M *ᵥ
      (fun r => algebraMap k ((algΓ (CommRingCat.of k)).obj T).unop (v r)) =
      c • (fun r => algebraMap k ((algΓ (CommRingCat.of k)).obj T).unop (v r)) := he
  change ∑ i, pointAlgebraHom G T g (b i : algebra G) *
    (M *ᵥ (fun r => algebraMap k ((algΓ (CommRingCat.of k)).obj T).unop (v r))) i =
      c * _
  rw [he', affineRegularCoordinateMap_apply, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, Algebra.smul_def]
  change _ * (c * algebraMap k ((algΓ (CommRingCat.of k)).obj T).unop (v i)) =
    c * (algebraMap k ((algΓ (CommRingCat.of k)).obj T).unop (v i) * _)
  ring

end Chevalley

namespace SplitPinning

open AffineCoordinates AffineLinearEmbedding Chevalley MatrixRepresentation

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)

local instance covariantRegularWeightsIsAffine2 : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance : IsAffine p.positiveUnipotent.X.left :=
  isAffine_of_isAffineHom p.positiveUnipotent.X.hom
local instance : IsAffineHom p.torus.toGrp.X.hom := p.isSplitTorus.isAffineHom

/-- Left covariance restricts to the supplied character on the torus. -/
theorem pointAlgebraHom_leftTorus_of_covariant
    {lam : characterLattice p.torus} {f : algebra G}
    (hf : f ∈ AffineCoordinates.leftCovariantSubspace p.negativeBorelHom
      (p.borelCharacterCoordinate lam))
    (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ p.torus.X) (g : T ⟶ G.X) :
    pointAlgebraHom G T ((s ≫ p.inclusion.hom.hom) * g) f =
      (show ((algΓ (CommRingCat.of k)).obj T).unop from
        (characterEval ((rationalCharacters.equivCharacterLattice p.torus).symm lam)
          T s : Γ(T.left, ⊤))) * pointAlgebraHom G T g f := by
  have h := pointAlgebraHom_leftCovariant p.negativeBorelHom
    (p.borelCharacterCoordinate lam) hf T (s ≫ p.torusToNegativeBorel.hom.hom) g
  rw [Category.assoc, ← Grp.comp_hom_hom, p.torusToNegativeBorel_comp,
    p.pointAlgebraHom_borelCharacterCoordinate, ← characterEval_characterRestrict,
    p.characterRestrict_torusToNegativeBorel_borelCharacter] at h
  exact h

variable (V : Submodule k (algebra G)) {d : ℕ} (b : Basis (Fin d) k V)

/-- Actual restriction to the positive unipotent subgroup in its Lie coordinates. -/
def covariantRegularRestriction : (Fin d → k) →ₗ[k] CharacterUnits.Coord p.positiveUnipotent :=
  (lieCoordinateEquiv p.positiveUnipotent).toLinearEquiv.toLinearMap.comp
    ((AffineHomImageHopfAdapter.pullback p.positiveUnipotentHom).hom.toAlgHom.toLinearMap.comp
      (affineRegularCoordinateMap G V b))

/-- Restriction is faithful on every covariant regular subspace. -/
theorem covariantRegularRestriction_injective {lam : characterLattice p.torus}
    (hcov : V ≤ AffineCoordinates.leftCovariantSubspace p.negativeBorelHom
      (p.borelCharacterCoordinate lam)) :
    Function.Injective (p.covariantRegularRestriction V b) := by
  intro v w he
  apply affineRegularCoordinateMap_injective G V b
  have he' := (lieCoordinateEquiv p.positiveUnipotent).injective he
  have hi := covariantCellRestriction_injective p.negativeBorelHom
    p.positiveUnipotentHom (p.borelCharacterCoordinate lam)
    p.cellCoordinate_mem_nonZeroDivisors p.exists_factors_of_isUnit_cellCoordinate
  have hh : (⟨affineRegularCoordinateMap G V b v,
      hcov (affineRegularCoordinateMap_mem G V b v)⟩ : leftCovariantSubspace
        p.negativeBorelHom (p.borelCharacterCoordinate lam)) =
      ⟨affineRegularCoordinateMap G V b w,
        hcov (affineRegularCoordinateMap_mem G V b w)⟩ := hi he'
  exact congrArg (fun z : leftCovariantSubspace p.negativeBorelHom
    (p.borelCharacterCoordinate lam) => (z : algebra G)) hh

/-- Evaluation of the restriction is evaluation on the actual subgroup point. -/
theorem covariantRegularRestriction_evaluate {A : CommAlgCat (CommRingCat.of k)}
    (v : Fin d → k) (x : p.positiveUnipotent.affinePoints A) :
    (Corepresented.affineSectionsAlgEquiv A).symm
      (Lie.pointCoordinates p.positiveUnipotent x (p.covariantRegularRestriction V b v)) =
      pointAlgebraHom G _ (x ≫ p.positiveUnipotentHom.hom.hom)
        (affineRegularCoordinateMap G V b v) := by
  change (Corepresented.affineSectionsAlgEquiv A).symm
    (Lie.pointCoordinates p.positiveUnipotent x (lieCoordinateEquiv p.positiveUnipotent
      (AffineHomImageHopfAdapter.pullback p.positiveUnipotentHom
        (affineRegularCoordinateMap G V b v)))) = _
  rw [← pointAlgebraHom_lieCoordinateEquiv,
    AffineHomImageHopfAdapter.pointAlgebraHom_pullback]
  rfl

variable (hV : letI := (bialgebra (corepresentation G)).toCoalgebra
      ∀ (ψ : Module.Dual k (algebra G)) (w : algebra G),
        w ∈ V → rightAct ψ w ∈ V)

/-- A torus weight vector restricts to a conjugation eigenfunction of weight
`lam - mu` on the actual positive unipotent subgroup. -/
theorem covariantRegularRestriction_mem_weightSpace {lam mu : characterLattice p.torus}
    (hcov : V ≤ leftCovariantSubspace p.negativeBorelHom (p.borelCharacterCoordinate lam))
    {v : Fin d → k}
    (hv : v ∈ p.representationWeightSpace (affineRegularRepresentation G V b hV) mu) :
    p.covariantRegularRestriction V b v ∈
      CoordinateWeights.weightSpace p.positiveUnipotentAction (lam - mu) := by
  intro A _ _ s x
  let T := (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) A))
  let E := (Corepresented.affineSectionsAlgEquiv (CommAlgCat.of (CommRingCat.of k) A)).symm
  apply E.injective
  rw [map_mul, covariantRegularRestriction_evaluate, covariantRegularRestriction_evaluate]
  rw [← characterEval_eq_section_characterValue]
  rw [p.positiveUnipotentAction_act_comp, ← GrpObj.inv_comp]
  rw [pointAlgebraHom_affineRegularCoordinateMap_mul_of_character G V b hV
    p.inclusion hv]
  rw [p.pointAlgebraHom_leftTorus_of_covariant
    (hcov (affineRegularCoordinateMap_mem G V b v))]
  have hχ : characterEval ((rationalCharacters.equivCharacterLattice p.torus).symm (lam - mu))
      T s = characterEval ((rationalCharacters.equivCharacterLattice p.torus).symm lam) T s *
        (characterEval ((rationalCharacters.equivCharacterLattice p.torus).symm mu) T s)⁻¹ := by
    change characterEval (lam - mu) T s = characterEval lam T s * (characterEval mu T s)⁻¹
    rw [sub_eq_add_neg, ← neg_one_zsmul mu, characterEval_add, characterEval_zsmul,
      zpow_neg_one]
  dsimp only [T] at hχ
  rw [hχ, Units.val_mul, map_inv]
  ring

/-- Every occurring weight in a covariant regular subspace lies below its left
character in the positive-root order. -/
theorem affineRegularRepresentation_weight_le {lam mu : characterLattice p.torus}
    (hcov : V ≤ leftCovariantSubspace p.negativeBorelHom (p.borelCharacterCoordinate lam))
    (hmu : p.representationWeightSpace (affineRegularRepresentation G V b hV) mu ≠ ⊥) :
    lam - mu ∈ p.positiveRootMonoid := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hmu
  apply p.mem_positiveRootMonoid_of_mem_weightSpace
    (p.covariantRegularRestriction_mem_weightSpace V b hV hcov hv)
  intro he
  apply hv0
  exact p.covariantRegularRestriction_injective V b hcov (he.trans
    (map_zero (p.covariantRegularRestriction V b)).symm)

end SplitPinning

end Langlands.GroupScheme
