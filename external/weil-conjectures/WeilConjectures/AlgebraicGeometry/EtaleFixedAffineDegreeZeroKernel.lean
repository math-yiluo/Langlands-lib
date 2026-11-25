/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.AbelianPullbackGlobalSectionsComparison
import WeilConjectures.AlgebraicGeometry.EtaleSetSectionAffineEventualEquality
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZero
import WeilConjectures.SixFunctors.BaseChange.GlobalSections

/-! # Finite-stage vanishing for one fixed sheaf in degree zero

Source: Stacks Project, Tags 09YQ, 0EYL, 04HR and 09YN.
(blueprint: lem-weil-pbc-fixed-affine-degree-zero-kernel).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- A degree-zero class of a single stage sheaf which dies on the affine inverse
limit dies after pullback to a later stage. No varying coefficient system or colimit
of sheaves is involved.

Source: Stacks Project, Tag 09YQ, degree-zero argument via 0EYL, 04HR and 09YN.
(blueprint: lem-weil-pbc-fixed-affine-degree-zero-kernel).

Proof: Restrict the inverse system to the cofinal upper tail of i. Its schemes and
limit are affine. Present the limit affine etale site as the colimit of the stage
sites (0EYL), and restrict the fixed sheaf and all its inverse images along the
small-to-affine equivalences (04HR). Inverse-image composition identifies the
pullbacks on the limit with the constant diagram on the limit inverse image of F;
these identifications commute with the units, so its identity cocone is a colimit.
Apply 09YN at the identity affine object. The resulting filtered colimit of stage
sections is the group of limit sections, with transition maps induced by the units.
The identification H^0 = sections carries cohomologyMap to these unit maps.
The zero image of x is therefore equality of its representative with zero in a
filtered colimit. The equality criterion supplies a stage on the upper tail where
the pulled-back representative is zero. The tail inclusion gives the displayed
arrow in I. For zero coefficients or an empty affine scheme, every section is zero;
for a singleton index, pullback along the limit projection is an equivalence.
-/
theorem fixed_affine_degree_zero_kernel
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : Iᵒᵖ, IsAffine (D.obj i)]
    [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
    (i : I) (F : Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (x : Sheaf.H F 0) (hx : cohomologyMap (c.π.app (op i)) F 0 x = 0) :
    ∃ (j : I) (f : i ⟶ j), cohomologyMap (D.map f.op) F 0 x = 0 := by
  classical
  let X := D.obj (op i)
  let g := (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology
    AddCommGrpCat.{u + 1} terminalIsTerminal).inv.app F
      ((Sheaf.H.equiv₀ F terminalIsTerminal) x)
  have hg : (Sheaf.H.equiv₀ F terminalIsTerminal).symm
      ((Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology
        AddCommGrpCat.{u + 1} terminalIsTerminal).hom.app F g) = x := by
    have h := Iso.inv_hom_id_apply
      ((Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology
        AddCommGrpCat.{u + 1} terminalIsTerminal).app F)
      ((Sheaf.H.equiv₀ F terminalIsTerminal) x)
    exact (congrArg (Sheaf.H.equiv₀ F terminalIsTerminal).symm h).trans
      ((Sheaf.H.equiv₀ F terminalIsTerminal).symm_apply_apply x)
  have hzero : globalSectionsUpperStarMap AddCommGrpCat.{u + 1}
      (c.π.app (op i)) F g = 0 := by
    rw [← hg, cohomologyMap_zero_eq_globalSectionsUpperStarMap] at hx
    have h := congrArg (Sheaf.H.equiv₀ _ terminalIsTerminal) hx
    simp only [AddEquiv.apply_symm_apply, map_zero] at h
    have h' := congrArg
      ((Sheaf.ΓNatIsoSheafSections c.pt.smallEtaleTopology
        AddCommGrpCat.{u + 1} terminalIsTerminal).inv.app _) h
    have hz := Iso.hom_inv_id_apply
      ((Sheaf.ΓNatIsoSheafSections c.pt.smallEtaleTopology
        AddCommGrpCat.{u + 1} terminalIsTerminal).app
        ((upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj F))
      (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} (c.π.app (op i)) F g)
    exact hz.symm.trans (h'.trans (map_zero _))
  obtain ⟨e, he⟩ := exists_abelianPullbackGlobalSectionsComparison X F
  have hcompare {Y Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X) (k : Z ⟶ X)
      (hk : h ≫ f = k)
      (s : (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj F) :
      e Z k (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} k F s) =
        etaleSetSectionComparison h f k hk
          ((sheafForget X.smallEtaleTopology).obj F) (⊤_ X.Etale)
          (e Y f (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} f F s)) := by
    have hh := he Y Z h f k hk (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} f F s)
    have hc' := globalSectionsUpperStarMap_comp' AddCommGrpCat.{u + 1} h f k hk.symm F
    have hv := ConcreteCategory.congr_hom hc' s
    simp only [ConcreteCategory.comp_apply] at hv
    erw [← hv] at hh
    have hi := Iso.hom_inv_id_apply
      ((Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{u + 1}).mapIso
        ((upperStarComp AddCommGrpCat.{u + 1} h f k hk.symm).app F))
      (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} k F s)
    exact (congrArg (e Z k) hi.symm).trans hh
  let j₀ : Over (op i) := Over.mk (𝟙 (op i))
  let s := e (D.obj j₀.left) (D.map j₀.hom)
    (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} (D.map j₀.hom) F g)
  let t := e (D.obj j₀.left) (D.map j₀.hom) 0
  have hst : etaleSetSectionComparison (c.π.app j₀.left) (D.map j₀.hom)
      (c.π.app (op i)) (c.w j₀.hom)
      ((sheafForget X.smallEtaleTopology).obj F) (⊤_ X.Etale) s =
      etaleSetSectionComparison (c.π.app j₀.left) (D.map j₀.hom)
        (c.π.app (op i)) (c.w j₀.hom)
        ((sheafForget X.smallEtaleTopology).obj F) (⊤_ X.Etale) t := by
    have hs' := hcompare (c.π.app j₀.left) (D.map j₀.hom)
      (c.π.app (op i)) (c.w j₀.hom) g
    have ht := he (D.obj j₀.left) c.pt (c.π.app j₀.left) (D.map j₀.hom)
      (c.π.app (op i)) (c.w j₀.hom) 0
    simp only [map_zero] at ht
    exact hs'.symm.trans ((congrArg (e c.pt (c.π.app (op i))) hzero).trans ht)
  have : IsIso (⊤_ X.Etale).hom := by
    let e₀ := terminalIsTerminal.uniqueUpToIso
      (MorphismProperty.Over.mkIdTerminal (@Etale) X)
    have : IsIso e₀.hom.left := inferInstance
    have he₀ : e₀.hom.left = (⊤_ X.Etale).hom := by
      have hw := e₀.hom.w
      change e₀.hom.left ≫ 𝟙 X = _ at hw
      exact (Category.comp_id _).symm.trans hw
    rw [← he₀]
    exact this
  let : IsAffine X := inferInstanceAs (IsAffine (D.obj (op i)))
  let : IsAffine (⊤_ X.Etale).left := IsAffine.of_isIso (Y := X) (⊤_ X.Etale).hom
  obtain ⟨k, a, b, ha⟩ := etaleSetSectionAffineEventualEquality D c hc i
    ((sheafForget X.smallEtaleTopology).obj F) (⊤_ X.Etale) j₀ j₀ s t hst
  have hab : b = a := by
    ext
    exact Subsingleton.elim _ _
  subst b
  let w : D.map a.left ≫ D.map j₀.hom = D.map k.hom :=
    (D.map_comp a.left j₀.hom).symm.trans (congrArg D.map a.w)
  have hk : globalSectionsUpperStarMap AddCommGrpCat.{u + 1} (D.map k.hom) F g = 0 := by
    have hs' := hcompare (D.map a.left) (D.map j₀.hom) (D.map k.hom) w g
    have ht' := he (D.obj j₀.left) (D.obj k.left) (D.map a.left) (D.map j₀.hom)
      (D.map k.hom) w 0
    simp only [map_zero] at ht'
    apply (e (D.obj k.left) (D.map k.hom)).injective
    exact hs'.trans (ha.trans ht'.symm)
  refine ⟨k.left.unop, k.hom.unop, ?_⟩
  rw [← hg, cohomologyMap_zero_eq_globalSectionsUpperStarMap]
  erw [hk]
  rw [map_zero, map_zero]

end AlgebraicGeometry.Etale
