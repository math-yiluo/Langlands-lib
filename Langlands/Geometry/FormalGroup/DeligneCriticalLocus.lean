import Langlands.Geometry.StructuralLineZeroReflection

/-! # Critical degrees of Deligne's actual tangent and lattice sheaves -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.DeligneFormalSpace

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

section Scalars

variable {S : Scheme.{u}}

private theorem structuralScalarEnd_one (M : S.Modules) : structuralScalarEnd M 1 = 𝟙 M := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  change (schemeScalar S (1 : Γ(S, ⊤))).val U • x = x
  simp [schemeScalar]

private theorem structuralScalarEnd_zero (M : S.Modules) : structuralScalarEnd M 0 = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  change (schemeScalar S (0 : Γ(S, ⊤))).val U • x = 0
  simp [schemeScalar]

private theorem structuralScalarEnd_comp (M : S.Modules) (a b : Γ(S, ⊤)) :
    structuralScalarEnd M a ≫ structuralScalarEnd M b = structuralScalarEnd M (b * a) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  change (schemeScalar S b).val U • ((schemeScalar S a).val U • x) =
    (schemeScalar S (b * a)).val U • x
  rw [smul_smul]
  change ((S.presheaf.map _).hom b * (S.presheaf.map _).hom a) • x =
    (S.presheaf.map _).hom (b * a) • x
  rw [map_mul]

private def structuralScalarEndIso (M : S.Modules) (a : (Γ(S, ⊤))ˣ) : M ≅ M where
  hom := structuralScalarEnd M a.val
  inv := structuralScalarEnd M a.inv
  hom_inv_id := by rw [structuralScalarEnd_comp, a.inv_val, structuralScalarEnd_one]
  inv_hom_id := by rw [structuralScalarEnd_comp, a.val_inv, structuralScalarEnd_one]

end Scalars

section FieldLines

variable {k : Type u} [Field k]

local notation "X" => Spec (CommRingCat.of k)

private theorem specField_scalar_isUnit {a : Γ(X, ⊤)} (ha : a ≠ 0) : IsUnit a := by
  let e := Scheme.ΓSpecIso (CommRingCat.of k)
  have he : e.hom a ≠ 0 := by
    intro hz
    apply ha
    apply (ConcreteCategory.bijective_of_isIso e.hom).injective
    simpa only [map_zero] using hz
  have h := he.isUnit.map e.inv.hom
  simpa using h

private theorem specField_scalar_eq_zero_of_isNilpotent {a : Γ(X, ⊤)} (ha : IsNilpotent a) :
    a = 0 := by
  let e := Scheme.ΓSpecIso (CommRingCat.of k)
  apply (ConcreteCategory.bijective_of_isIso e.hom).injective
  simpa only [map_zero] using (ha.map e.hom.hom).eq_zero

private theorem specField_line_id_ne_zero {M : Scheme.Modules X} (hM : IsLineSheaf X M) :
    𝟙 M ≠ 0 := by
  obtain ⟨e⟩ := hM.nonempty_unitIso
  intro h
  have h1 : structuralScalarEnd M 1 = 0 := (structuralScalarEnd_one M).trans h
  have he := congrArg (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom
    (structuralScalarEnd_eq_zero_of_unitIso e 1 h1)
  exact one_ne_zero (by simpa only [map_one, map_zero] using he)

/-- A nonzero morphism of actual line sheaves over a field is an isomorphism. -/
theorem specField_line_map_isIso_of_ne_zero {M N : Scheme.Modules X}
    (hM : IsLineSheaf X M) (hN : IsLineSheaf X N) (f : M ⟶ N) (hf : f ≠ 0) : IsIso f := by
  obtain ⟨eM⟩ := hM.nonempty_unitIso
  obtain ⟨eN⟩ := hN.nonempty_unitIso
  let g := eM.inv ≫ f ≫ eN.hom
  have hg : g ≠ 0 := by
    intro hz
    apply hf
    apply (cancel_epi eM.inv).mp
    apply (cancel_mono eN.hom).mp
    simpa [g, Category.assoc] using hz
  have ha : structuralUnitEndScalar g ≠ 0 := by
    intro hz
    apply hg
    rw [structuralUnitEnd_eq_scalar g, hz, structuralScalarEnd_zero]
  obtain ⟨a, h⟩ := specField_scalar_isUnit ha
  let e := eM ≪≫ structuralScalarEndIso (SheafOfModules.unit (Scheme.ringCatSheaf X)) a ≪≫ eN.symm
  have he : e.hom = f := by
    change eM.hom ≫ structuralScalarEnd (SheafOfModules.unit (Scheme.ringCatSheaf X))
      a.val ≫ eN.inv = f
    rw [h, ← structuralUnitEnd_eq_scalar g]
    simp [g]
  rw [← he]
  infer_instance

end FieldLines

section CriticalDegree

variable {S : Scheme.{u}} {d : ℕ} [NeZero d] {a : Γ(S, ⊤)}

namespace GradedPiSheaf

variable (M : GradedPiSheaf d S.sheaf (schemeScalar S a))

/-- The actual n-fold homogeneous tangent map, from degree i to degree i+n. -/
def componentPiIterate (i : ZMod d) : (n : ℕ) →
    M.componentSheaf i ⟶ M.componentSheaf (i + (n : ZMod d))
  | 0 => eqToHom (congrArg M.componentSheaf (by simp))
  | n + 1 => componentPiIterate i n ≫ M.componentPi (i + (n : ZMod d)) ≫
      eqToHom (congrArg M.componentSheaf (by simp [Nat.cast_add, add_assoc]))

private theorem componentTransport_inclusion {i j : ZMod d} (h : i = j) :
    eqToHom (congrArg M.componentSheaf h) ≫ M.componentInclusion j = M.componentInclusion i := by
  subst j
  simp

/-- The homogeneous tangent iterate is the restriction of the actual total Pi power. -/
@[reassoc]
theorem componentPiIterate_inclusion (i : ZMod d) (n : ℕ) :
    M.componentPiIterate i n ≫ M.componentInclusion (i + (n : ZMod d)) =
      M.componentInclusion i ≫ End.asHom (End.of M.pi ^ n) := by
  induction n with
  | zero => simp [componentPiIterate, M.componentTransport_inclusion]
  | succ n ih =>
    dsimp only [componentPiIterate]
    rw [Category.assoc, Category.assoc,
      M.componentTransport_inclusion (by simp [Nat.cast_add, add_assoc]),
      M.componentPi_inclusion, ← Category.assoc, ih, Category.assoc, pow_succ']
    rfl

end GradedPiSheaf

namespace LinePiSheaf

variable (M : LinePiSheaf d S a)

/-- A nonvanishing degree-one map on an actual residue fibre is invertible. -/
theorem isIso_fibrePi_of_ne_zero (i : ZMod d) (x : S) (hi : M.graded.fibrePi i x ≠ 0) :
    IsIso (M.graded.fibrePi i x) :=
  specField_line_map_isIso_of_ne_zero
    (IsLineSheaf.pullback (S.fromSpecResidueField x) (M.line i))
    (IsLineSheaf.pullback (S.fromSpecResidueField x) (M.line (i + 1))) _ hi

/-- Each point lies on at least one of the actual tangent Pi-zero loci. -/
theorem exists_mem_piZeroLocus (ha : IsNilpotent a) (x : S) :
    ∃ i : ZMod d, x ∈ M.graded.piZeroLocus i := by
  by_contra! h
  let f := S.fromSpecResidueField x
  let P := Scheme.Modules.pullback f
  have hPi (i : ZMod d) : IsIso (P.map (M.graded.componentPi i)) :=
    M.isIso_fibrePi_of_ne_zero i x (h i)
  have hIterate (n : ℕ) : IsIso (P.map (M.graded.componentPiIterate 0 n)) := by
    induction n with
    | zero =>
      unfold GradedPiSheaf.componentPiIterate
      infer_instance
    | succ n ih =>
      let _ := hPi (0 + (n : ZMod d))
      rw [GradedPiSheaf.componentPiIterate, Functor.map_comp, Functor.map_comp]
      infer_instance
  have hzero : f.appTop a = 0 := specField_scalar_eq_zero_of_isNilpotent (ha.map f.appTop.hom)
  have hpow : P.map (End.asHom ((End.of M.graded.pi) ^ d)) = 0 := by
    rw [M.graded.toPiSheaf.pi_pow_sheaf, pullback_structuralScalarEnd, hzero, structuralScalarEnd_zero]
  have he := congrArg P.map (M.graded.componentPiIterate_inclusion 0 d)
  rw [Functor.map_comp, Functor.map_comp, hpow, comp_zero] at he
  let _ := hIterate d
  let j : ZMod d := 0 + (d : ZMod d)
  have hIncl : M.graded.pullbackInclusion f j = 0 := by
    change P.map (M.graded.componentInclusion (0 + (d : ZMod d))) = 0
    apply (cancel_epi (P.map (M.graded.componentPiIterate 0 d))).mp
    simpa only [comp_zero] using he
  have hId := M.graded.pullbackInclusion_projection f j
  rw [hIncl, zero_comp] at hId
  exact specField_line_id_ne_zero (IsLineSheaf.pullback f (M.line j)) hId.symm

/-- The union is taken on the underlying scheme of the actual Deligne tangent datum. -/
theorem iUnion_piZeroLocus_eq_univ (ha : IsNilpotent a) :
    (⋃ i : ZMod d, M.graded.piZeroLocus i) = Set.univ :=
  Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr (M.exists_mem_piZeroLocus ha x)

end LinePiSheaf

end CriticalDegree

end Langlands.DeligneFormalSpace
