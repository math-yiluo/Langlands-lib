import Langlands.GroupScheme.Torus.DiagonalizableFaithfullyFlat
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Nonzero characters of split tori are fpqc quotients -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry

open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

namespace CharacterFpqc

/-! ### The lattice map `n ↦ n • m` -/

section Lattice

variable {I : Type u}

/-- The lattice map `ℤ → ℤ^I`, `n ↦ n • m`. The source `ℤ` is written as `PUnit → ℤ`, a
type in universe `u`. -/
def scaleHom (m : I → ℤ) : (PUnit.{u + 1} → ℤ) →+ (I → ℤ) :=
  (zmultiplesHom (I → ℤ) m).comp (Pi.evalAddMonoidHom (fun _ : PUnit.{u + 1} => ℤ) PUnit.unit)

theorem scaleHom_apply (m : I → ℤ) (f : PUnit.{u + 1} → ℤ) :
    scaleHom m f = f PUnit.unit • m :=
  rfl

theorem scaleHom_injective {m : I → ℤ} (hm : m ≠ 0) : Function.Injective (scaleHom m) := by
  intro f f' h
  funext t
  exact smul_left_injective ℤ hm h

end Lattice

/-! ### Points of the comparison isomorphisms -/

section Points

/-- On points, the splitting `D(Λ) ≅ 𝔾_m^J` is the chosen point model of `D(Λ)`. -/
theorem splitIso_hom_points (R : CommRingCat.{u}) {Λ : Type u} [AddCommGroup Λ] {J : Type u}
    [Fintype J] [DecidableEq J] (b : Λ ≃+ (J → ℤ)) (T : Over (Spec R))
    (x : T ⟶ (Diagonalizable.groupScheme R Λ).X) :
    splitTorus.pointsEquiv J T (x ≫ (Diagonalizable.splitIso R b).hom.hom.hom) =
      Diagonalizable.splitPointsEquiv R b T x :=
  isoOfPointModels_hom (fun T : Over (Spec R) => J → (Γ(T.left, ⊤))ˣ)
    (fun a => splitTorus.unitsRestrict J a) (Diagonalizable.splitPointsEquiv R b)
    (fun T => splitTorus.pointsEquiv J T) (Diagonalizable.splitPointsEquiv_naturality R b)
    (fun a y => splitTorus.pointsEquiv_naturality J a y) T x

/-- On points, `𝔾_m^{PUnit} ≅ 𝔾_m` reads off the only coordinate. -/
theorem gmIso_inv_points {S : Scheme.{u}} (T : Over S) (y : T ⟶ (splitTorus S PUnit.{u + 1}).X) :
    Gm.pointsEquiv S T (y ≫ (splitTorus.gmIso S).inv.hom.hom) =
      splitTorus.pointsEquiv PUnit.{u + 1} T y PUnit.unit := by
  have h := isoOfPointModels_inv (fun T : Over S => PUnit.{u + 1} → (Γ(T.left, ⊤))ˣ)
    (fun a => splitTorus.unitsRestrict PUnit a)
    (fun T => (Gm.pointsEquiv S T).trans
      (MulEquiv.piUnique fun _ : PUnit.{u + 1} => (Γ(T.left, ⊤))ˣ).symm)
    (fun T => splitTorus.pointsEquiv PUnit T)
    (fun a x => by
      funext i
      change Gm.pointsEquiv S _ (a ≫ x) = _
      rw [Gm.pointsEquiv_naturality]
      rfl)
    (fun a y => splitTorus.pointsEquiv_naturality PUnit a y) T y
  exact congrFun h PUnit.unit

end Points

/-! ### Characters of split tori as maps of diagonalizable group schemes -/

section Character

variable (k : Type u) [Field k] (I : Type u) [Fintype I] [DecidableEq I]

/-- Under `D(ℤ^I) ≅ 𝔾_m^I` and `D(ℤ) ≅ 𝔾_m`, the character `t ↦ ∏ tᵢ ^ mᵢ` is the map
`D(ℤ^I) → D(ℤ)` induced by the lattice map `n ↦ n • m`. -/
theorem splitIso_hom_comp_characterLatticeEquiv_symm (m : I → ℤ) :
    (Diagonalizable.splitIso (CommRingCat.of k) (AddEquiv.refl (I → ℤ))).hom ≫
        CommGroupScheme.groupHom ((splitTorus.characterLatticeEquiv k I).symm m) =
      Diagonalizable.restrictMap (CommRingCat.of k) (scaleHom m) ≫
        (Diagonalizable.splitIso (CommRingCat.of k) (AddEquiv.refl (PUnit.{u + 1} → ℤ))).hom ≫
          (splitTorus.gmIso _).inv := by
  apply hom_ext_points
  intro T x
  apply (Gm.pointsEquiv (Spec (CommRingCat.of k)) T).injective
  rw [Grp.comp_hom_hom, ← Category.assoc, splitTorus.pointsEquiv_characterLatticeEquiv_symm,
    splitIso_hom_points, Grp.comp_hom_hom, Grp.comp_hom_hom, ← Category.assoc, ← Category.assoc,
    gmIso_inv_points, splitIso_hom_points]
  have h1 := Diagonalizable.pointsEquiv_restrictMap (CommRingCat.of k) (scaleHom m) x
    (Pi.single PUnit.unit 1)
  rw [scaleHom_apply, Pi.single_eq_same, one_smul] at h1
  change _ = DFunLike.coe (F := Multiplicative (PUnit.{u + 1} → ℤ) →* _)
    (Corepresented.pointsEquiv (Diagonalizable.functor (CommRingCat.of k) (PUnit.{u + 1} → ℤ))
      (Diagonalizable.grpCorepresentation (CommRingCat.of k) (PUnit.{u + 1} → ℤ)) T
      (x ≫ (Diagonalizable.restrictMap (CommRingCat.of k) (scaleHom m)).hom.hom))
    (.ofAdd (Pi.single PUnit.unit 1))
  rw [h1]
  set χ := Corepresented.pointsEquiv (Diagonalizable.functor (CommRingCat.of k) (I → ℤ))
    (Diagonalizable.grpCorepresentation (CommRingCat.of k) (I → ℤ)) T x
  change ∏ i, Diagonalizable.charEquiv (AddEquiv.refl (I → ℤ)) _ χ i ^ m i =
    DFunLike.coe (F := Multiplicative (I → ℤ) →* _) χ (.ofAdd m)
  conv_rhs => rw [← (Diagonalizable.charEquiv (AddEquiv.refl (I → ℤ)) _).symm_apply_apply χ]
  rfl

end Character

end CharacterFpqc

open CharacterFpqc in
/-- A nonzero character of a split torus over a field is quasi-compact, flat and surjective. -/
theorem characterFpqc : CharacterFpqcStatement.{u} := by
  intro k _ S hS a ha
  obtain ⟨I, hI, ⟨e⟩⟩ := hS
  classical
  let _ : Fintype I := Fintype.ofFinite I
  let χ : characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) :=
    Additive.ofMul (e.inv ≫ CommGroupScheme.groupHom a)
  let E : S ⟶ splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I := Additive.ofMul e.hom
  have haχ : a = E ≫ χ := by
    change a = Additive.ofMul (e.hom ≫ e.inv ≫ CommGroupScheme.groupHom a)
    rw [e.hom_inv_id_assoc]
    rfl
  set m := splitTorus.characterLatticeEquiv k I χ with hm_def
  have hχ : χ = (splitTorus.characterLatticeEquiv k I).symm m := by
    rw [hm_def, AddEquiv.symm_apply_apply]
  have hm : m ≠ 0 := by
    intro h0
    apply ha
    rw [haχ, hχ, h0, map_zero, Limits.comp_zero]
  let E₁ := e ≪≫ (Diagonalizable.splitIso (CommRingCat.of k) (AddEquiv.refl (I → ℤ))).symm
  let E₂ := Diagonalizable.splitIso (CommRingCat.of k) (AddEquiv.refl (PUnit.{u + 1} → ℤ)) ≪≫
    (splitTorus.gmIso _).symm
  have ha' : CommGroupScheme.groupHom a =
      E₁.hom ≫ Diagonalizable.restrictMap (CommRingCat.of k) (scaleHom m) ≫ E₂.hom := by
    rw [haχ, hχ]
    change e.hom ≫ CommGroupScheme.groupHom ((splitTorus.characterLatticeEquiv k I).symm m) = _
    rw [(Iso.eq_inv_comp _).2 (splitIso_hom_comp_characterLatticeEquiv_symm k I m)]
    simp only [E₁, E₂, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  have hleft : (CommGroupScheme.groupHom a).hom.hom.left =
      E₁.hom.hom.hom.left ≫
        (Diagonalizable.restrictMap (CommRingCat.of k) (scaleHom m)).hom.hom.left ≫
          E₂.hom.hom.hom.left := by
    rw [ha']
    rfl
  have : IsIso E₁.hom.hom.hom.left := Functor.map_isIso (Grp.forget _ ⋙ Over.forget _) E₁.hom
  have : IsIso E₂.hom.hom.hom.left := Functor.map_isIso (Grp.forget _ ⋙ Over.forget _) E₂.hom
  have : Nontrivial (CommRingCat.of k) := inferInstanceAs (Nontrivial k)
  obtain ⟨hflat, hsurj⟩ := Diagonalizable.flat_and_surjective_restrictMap (CommRingCat.of k)
    (scaleHom m) (scaleHom_injective hm)
  have : QuasiCompact
      (Diagonalizable.restrictMap (CommRingCat.of k) (scaleHom m)).hom.hom.left := by
    have hqc : QuasiCompact (Spec.map (CommRingCat.ofHom
        (AddMonoidAlgebra.mapDomainRingHom (CommRingCat.of k) (scaleHom m)))) :=
      inferInstance
    rw [Diagonalizable.restrictMap_left]
    exact hqc
  rw [hleft]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end Langlands.GroupScheme.RelativeRoot
