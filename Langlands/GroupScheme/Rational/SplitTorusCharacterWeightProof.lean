import Langlands.GroupScheme.Rational.SplitTorusCharacterWeightStatement
import Langlands.GroupScheme.MatrixRepresentation.SplitTorusCharacterDecomposition
import Langlands.GroupScheme.AffineLinearEmbeddingCorepresentedProof

/-! # Prescribed characters occur in finite representations -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj Classical

namespace Langlands.GroupScheme

namespace MatrixRepresentation

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {n : Type} [Fintype n] [DecidableEq n]

/-- A character absent from a split-torus representation has zero coefficient
on every universal matrix entry. -/
theorem characterCoefficient_universalCharacterMatrix_eq_zero
    (hG : IsSplitTorus G) (ρ : MatrixRepresentation G n)
    (χ : rationalCharacters G) (hχ : ρ.characterSpace χ = ⊥) (r s : n) :
    characterCoefficient χ (ρ.universalCharacterMatrix r s) = 0 := by
  have hzero : ∀ v : n → k, ρ.characterProjector χ v = 0 := by
    intro v
    have hv : v ∈ ⨆ ψ, ρ.characterSpace ψ := by
      rw [iSup_characterSpace_eq_top_of_isSplitTorus hG ρ]
      trivial
    refine Submodule.iSup_induction ρ.characterSpace
      (motive := fun v => ρ.characterProjector χ v = 0) hv ?_ ?_ ?_
    · intro ψ v hv
      rw [characterProjector_of_mem ρ χ ψ hv]
      split_ifs with h
      · subst ψ
        exact (Submodule.mem_bot k).mp (hχ ▸ hv)
      · rfl
    · exact map_zero _
    · intro v w hv hw
      rw [map_add, hv, hw, add_zero]
  have h := congrFun (hzero (Pi.single s 1)) r
  simpa [characterProjector, universalCharacterAction, universalVector,
    Matrix.mulVec, dotProduct, Pi.single_apply, apply_ite] using h

end MatrixRepresentation

namespace SplitTorusCharacterWeight

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- Every coordinate function lies in the span of matrix coefficients of one
finite representation, with its actual pointwise evaluation formula. -/
theorem exists_coefficients (f : CharacterUnits.Coord G) :
    ∃ (n : ℕ) (ρ : MatrixRepresentation G (Fin n))
      (a : Matrix (Fin n) (Fin n) (CharacterUnits.Coord G)),
      f ∈ Submodule.span k (Set.range fun p : Fin n × Fin n => a p.1 p.2) ∧
      ∀ (A : CommAlgCat.{u} (CommRingCat.of k)) (x : G.affinePoints A) (r s : Fin n),
        (ρ.affineMatrix A x : Matrix (Fin n) (Fin n) A) r s =
          Lie.pointCoordinates G x (a r s) := by
  classical
  let e := AffineCorepresentation.corep G (Lie.coordinateIso G)
  obtain ⟨n, a, hmul, hone, hspan⟩ := Comodule.exists_matrix
    (Corepresented.LinearEmbedding.coassoc e)
    (Corepresented.LinearEmbedding.leftCounit e)
    (Corepresented.LinearEmbedding.rightCounit e) {f}
  let α := Corepresented.LinearEmbedding.toGL e a hmul hone
  let ρ : MatrixRepresentation G (Fin n) :=
    AffineCorepresentation.toModel G (Lie.coordinateIso G) ≫
      Corepresented.groupSchemeMap e
        (GeneralLinear.corepresentableBy (Fin n) (CommRingCat.of k)) α
  refine ⟨n, ρ, a, hspan f (Finset.mem_singleton_self f), ?_⟩
  intro A x r s
  have h := Corepresented.groupSchemeMap_affinePoints e
    (GeneralLinear.corepresentableBy (Fin n) (CommRingCat.of k)) α
    (x ≫ (Lie.coordinateIso G).inv)
  rw [AffineCorepresentation.affinePointsEquiv_eq] at h
  simp only [AffineCorepresentation.iso_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id] at h
  have h' := congrArg (fun z : GL (Fin n) A => (z : Matrix (Fin n) (Fin n) A) r s) h
  exact h'

/-- Restriction to a closed affine subgroup is surjective on the chosen
coordinate algebras. -/
theorem restriction_surjective
    {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]
    (i : H ⟶ G) (hi : IsClosedSubgroup i) :
    Function.Surjective
      (Lie.pointCoordinates G (CharacterUnits.universalPoint H ≫ i.hom.hom)) := by
  let p := Lie.pointCoordinates G (CharacterUnits.universalPoint H ≫ i.hom.hom)
  have hp := (Lie.pointCoordinates G).symm_apply_apply
    (CharacterUnits.universalPoint H ≫ i.hom.hom)
  change (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom p).op ≫
    (Lie.coordinateIso G).hom = CharacterUnits.universalPoint H ≫ i.hom.hom at hp
  have hmap : (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom p).op =
      (Lie.coordinateIso H).hom ≫ i.hom.hom ≫ (Lie.coordinateIso G).inv := by
    calc
      _ = ((algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom p).op ≫
          (Lie.coordinateIso G).hom) ≫ (Lie.coordinateIso G).inv := by simp
      _ = _ := by rw [hp, CharacterUnits.universalPoint_eq]; rfl
  let ψ := ((commAlgCatEquivUnder (CommRingCat.of k)).functor.map
    (CommAlgCat.ofHom p)).right
  have hψ : Spec.map ψ =
      (Lie.coordinateIso H).hom.left ≫ i.hom.hom.left ≫
        (Lie.coordinateIso G).inv.left := by
    simpa only [Over.comp_left, algSpec_map_left, Quiver.Hom.unop_op] using
      congrArg CommaMorphism.left hmap
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsIso (Lie.coordinateIso H).hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map (Lie.coordinateIso H).hom))
  have : IsIso (Lie.coordinateIso G).inv.left :=
    inferInstanceAs (IsIso ((Over.forget _).map (Lie.coordinateIso G).inv))
  have : IsClosedImmersion (Spec.map ψ) := by
    rw [hψ]
    infer_instance
  have hs := (IsClosedImmersion.isAffine_surjective_of_isAffine (Spec.map ψ)).2
  have he : (Scheme.ΓSpecIso _).inv ≫ (Spec.map ψ).appTop ≫
      (Scheme.ΓSpecIso _).hom = ψ := by
    rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  have hsurj : Function.Surjective
      ((Scheme.ΓSpecIso _).inv ≫ (Spec.map ψ).appTop ≫ (Scheme.ΓSpecIso _).hom) :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).hom).2.comp
      (hs.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).inv).2)
  rw [he] at hsurj
  exact hsurj

/-- Every character of a closed split torus occurs in a finite representation
of the ambient affine group scheme. -/
theorem exists_character_weight
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hT : IsSplitTorus T.toGrp) (hi : IsClosedSubgroup i) :
    letI := hT.isAffineHom
    ∀ χ : rationalCharacters T.toGrp,
      ∃ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)),
        (ρ.restrict i).characterSpace χ ≠ ⊥ := by
  have := hT.isAffineHom
  intro χ
  let p := Lie.pointCoordinates G (CharacterUnits.universalPoint T.toGrp ≫ i.hom.hom)
  obtain ⟨f, hf⟩ := restriction_surjective i hi
    (CharacterUnits.unit χ : CharacterUnits.Coord T.toGrp)
  obtain ⟨n, ρ, a, hspan, ha⟩ := exists_coefficients f
  refine ⟨n, ρ, ?_⟩
  intro hχ
  let L : CharacterUnits.Coord G →ₗ[k] k :=
    (MatrixRepresentation.characterCoefficient χ).comp p.toLinearMap
  have hL : ∀ r s, L (a r s) = 0 := by
    intro r s
    change MatrixRepresentation.characterCoefficient χ (p (a r s)) = 0
    have hentry : p (a r s) =
        (ρ.affineMatrix (CharacterUnits.Coord T.toGrp)
          (CharacterUnits.universalPoint T.toGrp ≫ i.hom.hom) :
            Matrix (Fin n) (Fin n) (CharacterUnits.Coord T.toGrp)) r s :=
      (ha _ _ r s).symm
    rw [hentry]
    change MatrixRepresentation.characterCoefficient χ
      ((ρ.restrict i).universalCharacterMatrix r s) = 0
    exact MatrixRepresentation.characterCoefficient_universalCharacterMatrix_eq_zero
      hT (ρ.restrict i) χ hχ r s
  have hker : Submodule.span k (Set.range fun q : Fin n × Fin n => a q.1 q.2) ≤
      LinearMap.ker L := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨⟨r, s⟩, rfl⟩
    exact hL r s
  have hz : MatrixRepresentation.characterCoefficient χ (p f) = 0 := hker hspan
  rw [show p f = (CharacterUnits.unit χ : CharacterUnits.Coord T.toGrp) from hf] at hz
  simp [MatrixRepresentation.characterCoefficient_unit] at hz

end SplitTorusCharacterWeight

/-- Every character of a closed split torus occurs in a finite representation,
and hence so does every character of a split pinning's maximal torus. -/
theorem splitTorusCharacterWeight : SplitTorusCharacterWeightStatement.{u} := by
  intro k _ G _
  refine ⟨SplitTorusCharacterWeight.exists_character_weight, ?_⟩
  intro p lam
  exact SplitTorusCharacterWeight.exists_character_weight p.torus p.inclusion
    p.isSplitTorus p.isMaximalTorus.2.1
    ((rationalCharacters.equivCharacterLattice p.torus).symm lam)

end Langlands.GroupScheme
