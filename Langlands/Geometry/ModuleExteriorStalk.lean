import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Mathlib.Topology.Sheaves.Sheafify

/-! # Exterior powers and actual module stalks -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.ModuleSheaf

open CategoryTheory CategoryTheory.Limits TopologicalSpace

variable {R : Type u} [CommRing R] {X : TopCat.{u}}
  (M : X.Presheaf (ModuleCat.{u} R)) (x : X)

/-- Finitely many actual module germs admit representatives on one neighborhood. -/
theorem exists_fin_germs_eq (n : ℕ)
    (v : Fin n → TopCat.Presheaf.stalk (C := ModuleCat.{u} R) M x) :
    ∃ (U : Opens X) (hx : x ∈ U) (s : Fin n → M.obj (.op U)),
      ∀ j, TopCat.Presheaf.germ M U x hx (s j) = v j := by
  induction n with
  | zero =>
      exact ⟨⊤, Set.mem_univ x, Fin.elim0, fun j => Fin.elim0 j⟩
  | succ n ih =>
      obtain ⟨U, hxU, s, hs⟩ := ih (Fin.tail v)
      obtain ⟨V, hxV, t, ht⟩ := TopCat.Presheaf.exists_germ_eq M (v 0)
      refine ⟨U ⊓ V, ⟨hxU, hxV⟩,
        Fin.cons (M.map (homOfLE inf_le_right).op t)
          (fun j => M.map (homOfLE inf_le_left).op (s j)), ?_⟩
      intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · exact (TopCat.Presheaf.germ_res_apply M
          (homOfLE inf_le_right) x ⟨hxU, hxV⟩ t).trans ht
      · exact (TopCat.Presheaf.germ_res_apply M
          (homOfLE inf_le_left) x ⟨hxU, hxV⟩ (s j)).trans (hs j)

/-- Equality of two finite families of germs holds on one common neighborhood. -/
theorem fin_germ_eq (n : ℕ) {U V : Opens X} (hxU : x ∈ U) (hxV : x ∈ V)
    (s : Fin n → M.obj (.op U)) (t : Fin n → M.obj (.op V))
    (h : ∀ j, TopCat.Presheaf.germ M U x hxU (s j) =
      TopCat.Presheaf.germ M V x hxV (t j)) :
    ∃ (W : Opens X) (_hxW : x ∈ W) (iU : W ⟶ U) (iV : W ⟶ V),
      ∀ j, M.map iU.op (s j) = M.map iV.op (t j) := by
  induction n with
  | zero =>
      exact ⟨U ⊓ V, ⟨hxU, hxV⟩, homOfLE inf_le_left, homOfLE inf_le_right,
        fun j => Fin.elim0 j⟩
  | succ n ih =>
      obtain ⟨W, hxW, iU, iV, hW⟩ := ih (Fin.tail s) (Fin.tail t) (fun j => h j.succ)
      obtain ⟨W', hxW', iU', iV', hW'⟩ :=
        TopCat.Presheaf.germ_eq M x hxU hxV (s 0) (t 0) (h 0)
      refine ⟨W ⊓ W', ⟨hxW, hxW'⟩, homOfLE inf_le_left ≫ iU,
        homOfLE inf_le_left ≫ iV, ?_⟩
      intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · have eU : homOfLE (show W ⊓ W' ≤ W from inf_le_left) ≫ iU =
            homOfLE (show W ⊓ W' ≤ W' from inf_le_right) ≫ iU' :=
          Subsingleton.elim _ _
        have eV : homOfLE (show W ⊓ W' ≤ W from inf_le_left) ≫ iV =
            homOfLE (show W ⊓ W' ≤ W' from inf_le_right) ≫ iV' :=
          Subsingleton.elim _ _
        rw [eU, eV, op_comp, op_comp, M.map_comp, M.map_comp]
        exact congrArg (M.map (homOfLE inf_le_right).op) hW'
      · rw [op_comp, op_comp, M.map_comp, M.map_comp]
        exact congrArg (M.map (homOfLE inf_le_left).op) (hW j)

/-- The sectionwise exterior-power presheaf. -/
def exteriorPresheaf (n : ℕ) : X.Presheaf (ModuleCat.{u} R) :=
  M ⋙ ModuleCat.exteriorPower.functor R n

/-- The canonical comparison from the exterior presheaf's stalk to the exterior of a stalk. -/
def exteriorStalkMap (n : ℕ) :
    TopCat.Presheaf.stalk (C := ModuleCat.{u} R) (exteriorPresheaf M n) x ⟶
      (TopCat.Presheaf.stalk (C := ModuleCat.{u} R) M x).exteriorPower n :=
  colimit.desc _ {
    pt := (TopCat.Presheaf.stalk (C := ModuleCat.{u} R) M x).exteriorPower n
    ι := {
      app U := ModuleCat.exteriorPower.map
        (TopCat.Presheaf.germ M U.unop.1 x U.unop.2) n
      naturality {U V} f := by
        change (ModuleCat.exteriorPower.functor R n).map
            (M.map ((OpenNhds.inclusion x).map f.unop).op) ≫
            (ModuleCat.exteriorPower.functor R n).map
              (TopCat.Presheaf.germ M V.unop.1 x V.unop.2) =
          (ModuleCat.exteriorPower.functor R n).map
              (TopCat.Presheaf.germ M U.unop.1 x U.unop.2) ≫ 𝟙 _
        rw [Category.comp_id, ← (ModuleCat.exteriorPower.functor R n).map_comp]
        exact congrArg ((ModuleCat.exteriorPower.functor R n).map)
          (TopCat.Presheaf.germ_res M ((OpenNhds.inclusion x).map f.unop) x V.unop.2) } }

/-- The comparison sends the germ of an exterior product to the exterior product of germs. -/
theorem exteriorStalkMap_germ (n : ℕ) (U : Opens X) (hx : x ∈ U) :
    TopCat.Presheaf.germ (exteriorPresheaf M n) U x hx ≫
        exteriorStalkMap M x n =
      ModuleCat.exteriorPower.map (TopCat.Presheaf.germ M U x hx) n :=
  colimit.ι_desc _ _

private def exteriorGerm (n : ℕ) (v : Fin n → TopCat.Presheaf.stalk (C := ModuleCat.{u} R) M x) :
    TopCat.Presheaf.stalk (C := ModuleCat.{u} R) (exteriorPresheaf M n) x := by
  let U := (exists_fin_germs_eq M x n v).choose
  let hx := (exists_fin_germs_eq M x n v).choose_spec.choose
  let s := (exists_fin_germs_eq M x n v).choose_spec.choose_spec.choose
  exact TopCat.Presheaf.germ (exteriorPresheaf M n) U x hx
    (exteriorPower.ιMulti R n s)

private theorem exteriorGerm_eq (n : ℕ) (v : Fin n → TopCat.Presheaf.stalk (C := ModuleCat.{u} R) M x)
    (U : Opens X) (hx : x ∈ U) (s : Fin n → M.obj (.op U))
    (hs : ∀ j, TopCat.Presheaf.germ M U x hx (s j) = v j) :
    exteriorGerm M x n v =
      TopCat.Presheaf.germ (exteriorPresheaf M n) U x hx
        (exteriorPower.ιMulti R n s) := by
  dsimp only [exteriorGerm]
  obtain ⟨W, hxW, iU, iV, hW⟩ := fin_germ_eq M x n
    (exists_fin_germs_eq M x n v).choose_spec.choose hx
    (exists_fin_germs_eq M x n v).choose_spec.choose_spec.choose s
    (fun j => ((exists_fin_germs_eq M x n v).choose_spec.choose_spec.choose_spec j).trans
      (hs j).symm)
  apply TopCat.Presheaf.germ_ext (exteriorPresheaf M n) W hxW iU iV
  change exteriorPower.map n (M.map iU.op).hom _ =
    exteriorPower.map n (M.map iV.op).hom _
  rw [exteriorPower.map_apply_ιMulti, exteriorPower.map_apply_ιMulti]
  congr 1
  exact funext hW

private theorem exteriorGerm_add (n : ℕ) [DecidableEq (Fin n)]
    (v : Fin n → TopCat.Presheaf.stalk (C := ModuleCat.{u} R) M x)
    (i : Fin n) (a b : TopCat.Presheaf.stalk (C := ModuleCat.{u} R) M x) :
    exteriorGerm M x n (Function.update v i (a + b)) =
      exteriorGerm M x n (Function.update v i a) +
        exteriorGerm M x n (Function.update v i b) := by
  classical
  obtain ⟨U, hx, s, hs⟩ := exists_fin_germs_eq M x (n + 2) (Fin.cons a (Fin.cons b v))
  let t : Fin n → M.obj (.op U) := fun j => s j.succ.succ
  have ht (j : Fin n) : TopCat.Presheaf.germ M U x hx (t j) = v j := hs j.succ.succ
  have ha : TopCat.Presheaf.germ M U x hx (s 0) = a := hs 0
  have hb : TopCat.Presheaf.germ M U x hx (s 1) = b := hs 1
  rw [exteriorGerm_eq M x n _ U hx (Function.update t i (s 0 + s 1))
        (fun j => by by_cases h : j = i <;> simp [Function.update, h, map_add, ha, hb, ht]),
      exteriorGerm_eq M x n _ U hx (Function.update t i (s 0))
        (fun j => by by_cases h : j = i <;> simp [Function.update, h, ha, ht]),
      exteriorGerm_eq M x n _ U hx (Function.update t i (s 1))
        (fun j => by by_cases h : j = i <;> simp [Function.update, h, hb, ht]),
      AlternatingMap.map_update_add, map_add]

private theorem exteriorGerm_smul (n : ℕ) [DecidableEq (Fin n)]
    (v : Fin n → TopCat.Presheaf.stalk (C := ModuleCat.{u} R) M x)
    (i : Fin n) (r : R) (a : TopCat.Presheaf.stalk (C := ModuleCat.{u} R) M x) :
    exteriorGerm M x n (Function.update v i (r • a)) =
      r • exteriorGerm M x n (Function.update v i a) := by
  classical
  obtain ⟨U, hx, s, hs⟩ := exists_fin_germs_eq M x (n + 1) (Fin.cons a v)
  let t : Fin n → M.obj (.op U) := Fin.tail s
  have ht (j : Fin n) : TopCat.Presheaf.germ M U x hx (t j) = v j := hs j.succ
  have ha : TopCat.Presheaf.germ M U x hx (s 0) = a := hs 0
  rw [exteriorGerm_eq M x n _ U hx (Function.update t i (r • s 0))
        (fun j => by by_cases h : j = i <;> simp [Function.update, h, ha, ht]),
      exteriorGerm_eq M x n _ U hx (Function.update t i (s 0))
        (fun j => by by_cases h : j = i <;> simp [Function.update, h, ha, ht]),
      AlternatingMap.map_update_smul, map_smul]

private theorem exteriorGerm_alternating (n : ℕ)
    (v : Fin n → TopCat.Presheaf.stalk (C := ModuleCat.{u} R) M x)
    (i j : Fin n) (h : v i = v j) (hij : i ≠ j) :
    exteriorGerm M x n v = 0 := by
  classical
  obtain ⟨U, hx, s, hs⟩ := exists_fin_germs_eq M x n v
  rw [exteriorGerm_eq M x n _ U hx (Function.update s i (s j))
      (fun k => by by_cases hk : k = i <;> simp [Function.update, hk, hs, h]),
    (exteriorPower.ιMulti R n).map_update_self s hij, map_zero]

/-- Exterior products of germs, defined on a common neighborhood, form an alternating map. -/
def exteriorStalkAlternating (n : ℕ) :
    (TopCat.Presheaf.stalk (C := ModuleCat.{u} R) M x).AlternatingMap
      (TopCat.Presheaf.stalk (C := ModuleCat.{u} R) (exteriorPresheaf M n) x) n where
  toFun := exteriorGerm M x n
  map_update_add' := exteriorGerm_add M x n
  map_update_smul' := exteriorGerm_smul M x n
  map_eq_zero_of_eq' := exteriorGerm_alternating M x n

/-- The alternating map is the actual germ of the exterior product of representatives. -/
theorem exteriorStalkAlternating_germs (n : ℕ) (U : Opens X) (hx : x ∈ U)
    (s : Fin n → M.obj (.op U)) :
    exteriorStalkAlternating M x n (fun j => TopCat.Presheaf.germ M U x hx (s j)) =
      TopCat.Presheaf.germ (exteriorPresheaf M n) U x hx (exteriorPower.ιMulti R n s) :=
  exteriorGerm_eq M x n _ U hx s (fun _ => rfl)

/-- The map in the reverse direction, induced by the actual alternating map on germs. -/
def exteriorStalkInv (n : ℕ) :
    (TopCat.Presheaf.stalk (C := ModuleCat.{u} R) M x).exteriorPower n ⟶
      TopCat.Presheaf.stalk (C := ModuleCat.{u} R) (exteriorPresheaf M n) x :=
  ModuleCat.exteriorPower.desc (exteriorStalkAlternating M x n)

/-- The inverse sends an exterior product of germs to their common-neighborhood product. -/
@[simp]
theorem exteriorStalkInv_mk (n : ℕ)
    (v : Fin n → TopCat.Presheaf.stalk (C := ModuleCat.{u} R) M x) :
    exteriorStalkInv M x n (exteriorPower.ιMulti R n v) =
      exteriorStalkAlternating M x n v :=
  ModuleCat.exteriorPower.desc_mk _ _

/-- The canonical comparison takes a common-neighborhood exterior product to that of germs. -/
theorem exteriorStalkMap_alternating (n : ℕ)
    (v : Fin n → TopCat.Presheaf.stalk (C := ModuleCat.{u} R) M x) :
    exteriorStalkMap M x n (exteriorStalkAlternating M x n v) =
      exteriorPower.ιMulti R n v := by
  obtain ⟨U, hx, s, hs⟩ := exists_fin_germs_eq M x n v
  rw [show exteriorStalkAlternating M x n v =
      TopCat.Presheaf.germ (exteriorPresheaf M n) U x hx (exteriorPower.ιMulti R n s) from
    exteriorGerm_eq M x n v U hx s hs]
  change (TopCat.Presheaf.germ (exteriorPresheaf M n) U x hx ≫
    exteriorStalkMap M x n) _ = _
  rw [exteriorStalkMap_germ]
  change exteriorPower.map n (TopCat.Presheaf.germ M U x hx).hom _ = _
  rw [exteriorPower.map_apply_ιMulti]
  congr 1
  exact funext hs

/-- The canonical map followed by its inverse is the identity on the actual stalk. -/
@[reassoc (attr := simp)]
theorem exteriorStalkMap_inv (n : ℕ) :
    exteriorStalkMap M x n ≫ exteriorStalkInv M x n = 𝟙 _ := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hx
  rw [← Category.assoc, exteriorStalkMap_germ, Category.comp_id]
  apply ModuleCat.exteriorPower.hom_ext
  apply ModuleCat.AlternatingMap.ext
  intro s
  change exteriorStalkInv M x n
      (exteriorPower.map n (TopCat.Presheaf.germ M U x hx).hom
        (exteriorPower.ιMulti R n s)) =
    TopCat.Presheaf.germ (exteriorPresheaf M n) U x hx (exteriorPower.ιMulti R n s)
  rw [exteriorPower.map_apply_ιMulti, exteriorStalkInv_mk]
  exact exteriorStalkAlternating_germs M x n U hx s

/-- The inverse followed by the canonical map is the identity on the exterior power. -/
@[reassoc (attr := simp)]
theorem exteriorStalkInv_map (n : ℕ) :
    exteriorStalkInv M x n ≫ exteriorStalkMap M x n = 𝟙 _ := by
  apply ModuleCat.exteriorPower.hom_ext
  apply ModuleCat.AlternatingMap.ext
  intro v
  change exteriorStalkMap M x n (exteriorStalkInv M x n (exteriorPower.ιMulti R n v)) = _
  rw [exteriorStalkInv_mk, exteriorStalkMap_alternating]
  rfl

/-- Exterior powers commute with actual module stalks, in all finite degrees. -/
def exteriorStalkIso (n : ℕ) :
    TopCat.Presheaf.stalk (C := ModuleCat.{u} R) (exteriorPresheaf M n) x ≅
      (TopCat.Presheaf.stalk (C := ModuleCat.{u} R) M x).exteriorPower n where
  hom := exteriorStalkMap M x n
  inv := exteriorStalkInv M x n
  hom_inv_id := exteriorStalkMap_inv M x n
  inv_hom_id := exteriorStalkInv_map M x n

/-- The stalk comparison commutes with every morphism of the original presheaves. -/
@[reassoc]
theorem exteriorStalkMap_naturality {N : X.Presheaf (ModuleCat.{u} R)}
    (f : M ⟶ N) (n : ℕ) :
    (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} R) x).map
        (Functor.whiskerRight f (ModuleCat.exteriorPower.functor R n)) ≫
        exteriorStalkMap N x n =
      exteriorStalkMap M x n ≫ ModuleCat.exteriorPower.map
        ((TopCat.Presheaf.stalkFunctor (ModuleCat.{u} R) x).map f) n := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hx
  rw [← Category.assoc, TopCat.Presheaf.stalkFunctor_map_germ]
  change (ModuleCat.exteriorPower.functor R n).map (f.app (.op U)) ≫
      TopCat.Presheaf.germ (exteriorPresheaf N n) U x hx ≫ exteriorStalkMap N x n =
    TopCat.Presheaf.germ (exteriorPresheaf M n) U x hx ≫
      exteriorStalkMap M x n ≫ ModuleCat.exteriorPower.map
        ((TopCat.Presheaf.stalkFunctor (ModuleCat.{u} R) x).map f) n
  rw [exteriorStalkMap_germ, ← Category.assoc, exteriorStalkMap_germ]
  change (ModuleCat.exteriorPower.functor R n).map (f.app (.op U)) ≫
      (ModuleCat.exteriorPower.functor R n).map (TopCat.Presheaf.germ N U x hx) =
    (ModuleCat.exteriorPower.functor R n).map (TopCat.Presheaf.germ M U x hx) ≫
      (ModuleCat.exteriorPower.functor R n).map
        ((TopCat.Presheaf.stalkFunctor (ModuleCat.{u} R) x).map f)
  rw [← Functor.map_comp, ← Functor.map_comp, TopCat.Presheaf.stalkFunctor_map_germ]

/-- The actual exterior-power sheaf: sheafification of the sectionwise exterior presheaf. -/
def exteriorSheaf (n : ℕ) : X.Sheaf (ModuleCat.{u} R) :=
  (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)).obj
    (exteriorPresheaf M n)

/-- The exterior sheaf's stalk is the exterior power of the original stalk. -/
def exteriorSheafStalkIso (n : ℕ) :
    TopCat.Presheaf.stalk (C := ModuleCat.{u} R) (exteriorSheaf M n).obj x ≅
      (TopCat.Presheaf.stalk (C := ModuleCat.{u} R) M x).exteriorPower n := by
  letI := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x
    (ModuleCat.{u} R) (exteriorPresheaf M n)
  exact (asIso ((TopCat.Presheaf.stalkFunctor (ModuleCat.{u} R) x).map
    (toSheafify (Opens.grothendieckTopology X) (exteriorPresheaf M n)))).symm ≪≫
      exteriorStalkIso M x n

/-- The exterior sheaf comparison extends the canonical presheaf stalk map. -/
@[reassoc (attr := simp)]
theorem toSheafify_exteriorSheafStalkIso (n : ℕ) :
    (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} R) x).map
        (toSheafify (Opens.grothendieckTopology X) (exteriorPresheaf M n)) ≫
        (exteriorSheafStalkIso M x n).hom = exteriorStalkMap M x n := by
  simp [exteriorSheafStalkIso, exteriorStalkIso]

/-- The sheaf comparison takes sheafified germs to exterior products of original germs. -/
@[reassoc]
theorem exteriorSheafStalkIso_germ (n : ℕ) (U : Opens X) (hx : x ∈ U) :
    (toSheafify (Opens.grothendieckTopology X) (exteriorPresheaf M n)).app (.op U) ≫
        TopCat.Presheaf.germ (exteriorSheaf M n).obj U x hx ≫
        (exteriorSheafStalkIso M x n).hom =
      ModuleCat.exteriorPower.map (TopCat.Presheaf.germ M U x hx) n := by
  have h := congrArg (fun f => f ≫ (exteriorSheafStalkIso M x n).hom)
    (TopCat.Presheaf.stalkFunctor_map_germ U x hx
      (toSheafify (Opens.grothendieckTopology X) (exteriorPresheaf M n)))
  simpa only [Category.assoc, toSheafify_exteriorSheafStalkIso,
    exteriorStalkMap_germ, CategoryTheory.sheafify, exteriorSheaf] using h.symm

end Langlands.ModuleSheaf
