import Langlands.Algebra.NonUnitalBimoduleTensor
import Langlands.Algebra.NondegenerateModuleAdditive

/-!
# Actual one-sided tensor functors and Renard's F and P

The original balancing quotient and its named residual left action, with no
unit law. The intrinsic output nondegeneracy uses only the first left action.
Renard (9 July 2026), I.2.3, printed pp.17–18 / PDF pp.23–24.
-/

set_option autoImplicit false

namespace Langlands.Algebra.NondegenerateTensorFunctor

open CategoryTheory MulOpposite
open NonUnitalModuleTensor (Tensor tmul)

universe uS uR uX uA uB v w z

section Ambient

variable {S : Type uS} {R : Type uR} [NonUnitalRing S] [NonUnitalRing R]
  {X : Type uX} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
  (hX : ActionsCommute S R X)

/-- Bundle exactly the original tensor group with the published left action. -/
def tensorObj (M : Type v) [AddCommGroup M] [NonUnitalModule R M] :
    NonUnitalModuleCat.{uS, max uX v} S :=
  @NonUnitalModuleCat.of S _ (Tensor R X M) (NonUnitalModuleTensor.addCommGroup R X M)
    (NonUnitalBimoduleTensor.leftModule hX M)

theorem tensorObj_carrier (M : Type v) [AddCommGroup M] [NonUnitalModule R M] :
    (tensorObj hX M).carrier = Tensor R X M := rfl

theorem tensorObj_addCommGroup (M : Type v) [AddCommGroup M] [NonUnitalModule R M] :
    (tensorObj hX M).isAddCommGroup = NonUnitalModuleTensor.addCommGroup R X M := rfl

theorem tensorObj_module (M : Type v) [AddCommGroup M] [NonUnitalModule R M] :
    (tensorObj hX M).isModule = NonUnitalBimoduleTensor.leftModule hX M := rfl

variable {M : Type v} {N : Type w} {P : Type z}
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [NonUnitalModule R M] [NonUnitalModule R N] [NonUnitalModule R P]

/-- The whole original S-intertwiner is the published one-sided tensor map. -/
def map (f : NonUnitalModuleHom R M N) :
    NonUnitalModuleHom S (tensorObj hX M) (tensorObj hX N) :=
  NonUnitalBimoduleTensor.leftMap hX hX (NonUnitalBimoduleHom.id S R X) f

theorem map_def (f : NonUnitalModuleHom R M N) :
    map hX f = NonUnitalBimoduleTensor.leftMap hX hX
      (NonUnitalBimoduleHom.id S R X) f := rfl

theorem map_toAddMonoidHom (f : NonUnitalModuleHom R M N) :
    (map hX f).toAddMonoidHom =
      NonUnitalModuleTensor.map R (NonUnitalModuleHom.id Rᵐᵒᵖ X) f := rfl

@[simp] theorem map_tmul (f : NonUnitalModuleHom R M N) (x : X) (m : M) :
    map hX f (tmul R X M x m) = tmul R X N x (f m) := rfl

/-- Extensionality retains the named tensor groups and residual modules. -/
theorem hom_ext {f g : NonUnitalModuleHom S (tensorObj hX M) (tensorObj hX N)}
    (h : ∀ x m, f (tmul R X M x m) = g (tmul R X M x m)) : f = g := by
  have he := NonUnitalModuleTensor.hom_ext R h
  exact NonUnitalModuleHom.ext (DFunLike.congr_fun he)

theorem map_id : map hX (NonUnitalModuleHom.id R M) =
    NonUnitalModuleHom.id S (tensorObj hX M) :=
  hom_ext hX fun _ _ => rfl

theorem map_comp (g : NonUnitalModuleHom R N P) (f : NonUnitalModuleHom R M N) :
    map hX (g.comp f) = (map hX g).comp (map hX f) :=
  hom_ext hX fun _ _ => rfl

theorem map_zero : map hX (0 : NonUnitalModuleHom R M N) = 0 :=
  hom_ext hX fun x _ => NonUnitalModuleTensor.tmul_zero R X N x

theorem map_add (f g : NonUnitalModuleHom R M N) :
    map hX (f + g) = map hX f + map hX g :=
  hom_ext hX fun x m => NonUnitalModuleTensor.tmul_add R X N x (f m) (g m)

/-- The actual Hom map is additive, also at unequal source and target universes. -/
def mapAddHom : NonUnitalModuleHom R M N →+
    NonUnitalModuleHom S (tensorObj hX M) (tensorObj hX N) where
  toFun := map hX
  map_zero' := map_zero hX
  map_add' := map_add hX

/-- Fixed first factor on all original left modules; no right action on M. -/
def functor : NonUnitalModuleCat.{uR, v} R ⥤ NonUnitalModuleCat.{uS, max uX v} S where
  obj M := tensorObj hX M
  map f := map hX f
  map_id _ := map_id hX
  map_comp f g := map_comp hX g f

instance functor_additive : (functor.{uS, uR, uX, v} hX).Additive where
  map_add {_ _ f g} := map_add hX f g

theorem functor_obj (M : NonUnitalModuleCat.{uR, v} R) :
    (functor hX).obj M = tensorObj hX M := rfl

theorem functor_obj_carrier (M : NonUnitalModuleCat.{uR, v} R) :
    ((functor hX).obj M).carrier = Tensor R X M := rfl

theorem functor_obj_addCommGroup (M : NonUnitalModuleCat.{uR, v} R) :
    ((functor hX).obj M).isAddCommGroup = NonUnitalModuleTensor.addCommGroup R X M := rfl

theorem functor_obj_module (M : NonUnitalModuleCat.{uR, v} R) :
    ((functor hX).obj M).isModule = NonUnitalBimoduleTensor.leftModule hX M := rfl

theorem functor_map {M N : NonUnitalModuleCat.{uR, v} R} (f : M ⟶ N) :
    (functor hX).map f = NonUnitalBimoduleTensor.leftMap hX hX
      (NonUnitalBimoduleHom.id S R X) f := rfl

theorem functor_map_toAddMonoidHom {M N : NonUnitalModuleCat.{uR, v} R} (f : M ⟶ N) :
    ((functor hX).map f).toAddMonoidHom =
      NonUnitalModuleTensor.map R (NonUnitalModuleHom.id Rᵐᵒᵖ X) f := rfl

theorem functor_map_tmul {M N : NonUnitalModuleCat.{uR, v} R} (f : M ⟶ N) (x : X) (m : M) :
    ((functor hX).map f).toAddMonoidHom (tmul R X M x m) =
      tmul R X N x (f.toAddMonoidHom m) := rfl

theorem functor_mapAddHom (M N : NonUnitalModuleCat.{uR, v} R) :
    (functor hX).mapAddHom (X := M) (Y := N) = mapAddHom hX := rfl

end Ambient

section Nondegenerate

variable {S : Type uS} {R : Type uR} [NonUnitalRing S] [NonUnitalRing R]
  {X : Type uX} [AddCommGroup X] [NonUnitalModule S X] [NonUnitalModule Rᵐᵒᵖ X]
  (hS : IsIdempotented S) (hX : ActionsCommute S R X) (hnd : IsNondegenerate S X)

include hS hnd

/-- Intrinsic output nondegeneracy: neither the second factor nor the first right
 action is assumed nondegenerate, and R need not be idempotented. -/
theorem isNondegenerate (M : Type v) [AddCommGroup M] [NonUnitalModule R M] :
    @IsNondegenerate S (Tensor R X M) _ (NonUnitalModuleTensor.addCommGroup R X M)
      (NonUnitalBimoduleTensor.leftModule hX M) := by
  let := NonUnitalBimoduleTensor.leftModule hX M
  intro t
  change t ∈ nondegeneratePart hS (Tensor R X M)
  obtain ⟨q, rfl⟩ := NonUnitalModuleTensor.projection_surjective R X M t
  refine TensorProduct.inductionOn q ?_ ?_
  · intro x m
    obtain ⟨e, he⟩ := hnd x
    refine ⟨e, ?_⟩
    change tmul R X M ((e : S) • x) m = tmul R X M x m
    rw [he]
  · intro q r hq hr
    rw [_root_.map_add]
    exact (nondegeneratePart hS (Tensor R X M)).toAddSubgroup.add_mem hq hr

/-- Lift the same objects and original maps to the actual nondegenerate full subcategory. -/
def nondegenerateFunctor :
    NonUnitalModuleCat.{uR, v} R ⥤ NondegenerateModuleCat.{uS, max uX v} S where
  obj M := ⟨tensorObj hX M, isNondegenerate hS hX hnd M⟩
  map f := ObjectProperty.homMk (map hX f)
  map_id _ := by
    apply ObjectProperty.hom_ext
    exact map_id hX
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact map_comp hX g f

instance nondegenerateFunctor_additive :
    (nondegenerateFunctor.{uS, uR, uX, v} hS hX hnd).Additive where
  map_add := by
    intro M N f g
    apply ObjectProperty.hom_ext
    exact map_add hX f g

theorem nondegenerateFunctor_obj (M : NonUnitalModuleCat.{uR, v} R) :
    ((nondegenerateFunctor hS hX hnd).obj M).obj = tensorObj hX M := rfl

theorem nondegenerateFunctor_obj_carrier (M : NonUnitalModuleCat.{uR, v} R) :
    ((nondegenerateFunctor hS hX hnd).obj M).obj.carrier = Tensor R X M := rfl

theorem nondegenerateFunctor_obj_addCommGroup (M : NonUnitalModuleCat.{uR, v} R) :
    ((nondegenerateFunctor hS hX hnd).obj M).obj.isAddCommGroup =
      NonUnitalModuleTensor.addCommGroup R X M := rfl

theorem nondegenerateFunctor_obj_module (M : NonUnitalModuleCat.{uR, v} R) :
    ((nondegenerateFunctor hS hX hnd).obj M).obj.isModule =
      NonUnitalBimoduleTensor.leftModule hX M := rfl

theorem nondegenerateFunctor_map_hom {M N : NonUnitalModuleCat.{uR, v} R} (f : M ⟶ N) :
    ((nondegenerateFunctor hS hX hnd).map f).hom =
      NonUnitalBimoduleTensor.leftMap hX hX (NonUnitalBimoduleHom.id S R X) f := rfl

theorem nondegenerateFunctor_map_toAddMonoidHom {M N : NonUnitalModuleCat.{uR, v} R}
    (f : M ⟶ N) :
    ((nondegenerateFunctor hS hX hnd).map f).hom.toAddMonoidHom =
      NonUnitalModuleTensor.map R (NonUnitalModuleHom.id Rᵐᵒᵖ X) f := rfl

theorem nondegenerateFunctor_map_tmul {M N : NonUnitalModuleCat.{uR, v} R}
    (f : M ⟶ N) (x : X) (m : M) :
    ((nondegenerateFunctor hS hX hnd).map f).hom.toAddMonoidHom (tmul R X M x m) =
      tmul R X N x (f.toAddMonoidHom m) := rfl

/-- Equality of the whole functors, including every ambient original Hom. -/
theorem nondegenerateFunctor_comp_inclusion :
    nondegenerateFunctor.{uS, uR, uX, v} hS hX hnd ⋙ nondegenerateInclusion S =
      functor hX := rfl

/-- Restriction along the actual source inclusion, on the same tensor carriers and maps. -/
def restrictedFunctor :
    NondegenerateModuleCat.{uR, v} R ⥤ NondegenerateModuleCat.{uS, max uX v} S :=
  nondegenerateInclusion R ⋙ nondegenerateFunctor hS hX hnd

instance restrictedFunctor_additive :
    (restrictedFunctor.{uS, uR, uX, v} hS hX hnd).Additive where
  map_add := by
    intro M N f g
    apply ObjectProperty.hom_ext
    exact map_add hX f.hom g.hom

theorem restrictedFunctor_obj (M : NondegenerateModuleCat.{uR, v} R) :
    ((restrictedFunctor hS hX hnd).obj M).obj = tensorObj hX M.obj := rfl

theorem restrictedFunctor_obj_carrier (M : NondegenerateModuleCat.{uR, v} R) :
    ((restrictedFunctor hS hX hnd).obj M).obj.carrier = Tensor R X M.obj := rfl

theorem restrictedFunctor_obj_addCommGroup (M : NondegenerateModuleCat.{uR, v} R) :
    ((restrictedFunctor hS hX hnd).obj M).obj.isAddCommGroup =
      NonUnitalModuleTensor.addCommGroup R X M.obj := rfl

theorem restrictedFunctor_obj_module (M : NondegenerateModuleCat.{uR, v} R) :
    ((restrictedFunctor hS hX hnd).obj M).obj.isModule =
      NonUnitalBimoduleTensor.leftModule hX M.obj := rfl

theorem restrictedFunctor_map_hom {M N : NondegenerateModuleCat.{uR, v} R} (f : M ⟶ N) :
    ((restrictedFunctor hS hX hnd).map f).hom =
      NonUnitalBimoduleTensor.leftMap hX hX (NonUnitalBimoduleHom.id S R X) f.hom := rfl

theorem restrictedFunctor_map_toAddMonoidHom {M N : NondegenerateModuleCat.{uR, v} R}
    (f : M ⟶ N) :
    ((restrictedFunctor hS hX hnd).map f).hom.toAddMonoidHom =
      NonUnitalModuleTensor.map R (NonUnitalModuleHom.id Rᵐᵒᵖ X) f.hom := rfl

theorem restrictedFunctor_map_tmul {M N : NondegenerateModuleCat.{uR, v} R}
    (f : M ⟶ N) (x : X) (m : M.obj) :
    ((restrictedFunctor hS hX hnd).map f).hom.toAddMonoidHom (tmul R X M.obj x m) =
      tmul R X N.obj x (f.hom.toAddMonoidHom m) := rfl

end Nondegenerate

section Source

variable {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]

/-- The source's two-sided hypothesis supplies the one-sided input actually used. -/
theorem leftNondegenerate_of_bimodule
    {Y : Type uX} [AddCommGroup Y] [NonUnitalModule A Y] [NonUnitalModule Bᵐᵒᵖ Y]
    (h : IsNondegenerateBimodule A B Y) : IsNondegenerate A Y := h.1

/-- Left multiplication on an idempotented ring is intrinsically nondegenerate. -/
theorem regular_isNondegenerate (hB : IsIdempotented B) :
    @IsNondegenerate B B _ _ (NonUnitalModule.regular B) := by
  intro b
  obtain ⟨e, he⟩ := hB.exists_mem_corner b
  exact ⟨e, ((Idempotent.mem_corner_iff e b).mp he).1⟩

/-- Right multiplication uses the same two-sided local idempotent, on the right. -/
theorem rightRegular_isNondegenerate (hB : IsIdempotented B) :
    @IsRightNondegenerate B B _ _ (NonUnitalModule.rightRegular B) := by
  intro b
  obtain ⟨e, he⟩ := hB.exists_mem_corner b
  exact ⟨⟨op (e : B), congrArg op e.property⟩,
    ((Idempotent.mem_corner_iff e b).mp he).2⟩

section F

variable [NonUnitalModule A B] [NonUnitalModule Bᵐᵒᵖ B]
  (hA : IsIdempotented A) (hAB : ActionsCommute A B B)
  (hnd : IsNondegenerateBimodule A B B)

/-- Renard's F for specified commuting, two-sided nondegenerate actions on B. -/
def F : NondegenerateModuleCat.{uB, v} B ⥤
    NondegenerateModuleCat.{uA, max uB v} A :=
  restrictedFunctor hA hAB (leftNondegenerate_of_bimodule hnd)

instance F_additive : (F.{uA, uB, v} hA hAB hnd).Additive :=
  restrictedFunctor_additive hA hAB hnd.1

theorem F_eq_restrictedFunctor :
    F.{uA, uB, v} hA hAB hnd = restrictedFunctor hA hAB hnd.1 := rfl

theorem F_eq_inclusion_comp :
    F.{uA, uB, v} hA hAB hnd =
      nondegenerateInclusion B ⋙ nondegenerateFunctor hA hAB hnd.1 := rfl

theorem F_obj (N : NondegenerateModuleCat.{uB, v} B) :
    ((F hA hAB hnd).obj N).obj = tensorObj hAB N.obj := rfl

theorem F_obj_carrier (N : NondegenerateModuleCat.{uB, v} B) :
    ((F hA hAB hnd).obj N).obj.carrier = Tensor B B N.obj := rfl

theorem F_obj_addCommGroup (N : NondegenerateModuleCat.{uB, v} B) :
    ((F hA hAB hnd).obj N).obj.isAddCommGroup =
      NonUnitalModuleTensor.addCommGroup B B N.obj := rfl

theorem F_obj_module (N : NondegenerateModuleCat.{uB, v} B) :
    ((F hA hAB hnd).obj N).obj.isModule =
      NonUnitalBimoduleTensor.leftModule hAB N.obj := rfl

theorem F_map_hom {M N : NondegenerateModuleCat.{uB, v} B} (f : M ⟶ N) :
    ((F hA hAB hnd).map f).hom =
      NonUnitalBimoduleTensor.leftMap hAB hAB (NonUnitalBimoduleHom.id A B B) f.hom := rfl

theorem F_map_toAddMonoidHom {M N : NondegenerateModuleCat.{uB, v} B} (f : M ⟶ N) :
    ((F hA hAB hnd).map f).hom.toAddMonoidHom =
      NonUnitalModuleTensor.map B (NonUnitalModuleHom.id Bᵐᵒᵖ B) f.hom := rfl

theorem F_map_tmul {M N : NondegenerateModuleCat.{uB, v} B}
    (f : M ⟶ N) (b : B) (m : M.obj) :
    ((F hA hAB hnd).map f).hom.toAddMonoidHom (tmul B B M.obj b m) =
      tmul B B N.obj b (f.hom.toAddMonoidHom m) := rfl

end F

section P

variable [NonUnitalModule B B] [NonUnitalModule Aᵐᵒᵖ B]
  (hB : IsIdempotented B) (hBA : ActionsCommute B A B)
  (hnd : IsNondegenerateBimodule B A B)

/-- Renard's P for specified commuting, two-sided nondegenerate actions on B. -/
def P : NondegenerateModuleCat.{uA, v} A ⥤
    NondegenerateModuleCat.{uB, max uB v} B :=
  restrictedFunctor hB hBA (leftNondegenerate_of_bimodule hnd)

instance P_additive : (P.{uA, uB, v} hB hBA hnd).Additive :=
  restrictedFunctor_additive hB hBA hnd.1

theorem P_eq_restrictedFunctor :
    P.{uA, uB, v} hB hBA hnd = restrictedFunctor hB hBA hnd.1 := rfl

theorem P_eq_inclusion_comp :
    P.{uA, uB, v} hB hBA hnd =
      nondegenerateInclusion A ⋙ nondegenerateFunctor hB hBA hnd.1 := rfl

theorem P_obj (M : NondegenerateModuleCat.{uA, v} A) :
    ((P hB hBA hnd).obj M).obj = tensorObj hBA M.obj := rfl

theorem P_obj_carrier (M : NondegenerateModuleCat.{uA, v} A) :
    ((P hB hBA hnd).obj M).obj.carrier = Tensor A B M.obj := rfl

theorem P_obj_addCommGroup (M : NondegenerateModuleCat.{uA, v} A) :
    ((P hB hBA hnd).obj M).obj.isAddCommGroup =
      NonUnitalModuleTensor.addCommGroup A B M.obj := rfl

theorem P_obj_module (M : NondegenerateModuleCat.{uA, v} A) :
    ((P hB hBA hnd).obj M).obj.isModule =
      NonUnitalBimoduleTensor.leftModule hBA M.obj := rfl

theorem P_map_hom {M N : NondegenerateModuleCat.{uA, v} A} (f : M ⟶ N) :
    ((P hB hBA hnd).map f).hom =
      NonUnitalBimoduleTensor.leftMap hBA hBA (NonUnitalBimoduleHom.id B A B) f.hom := rfl

theorem P_map_toAddMonoidHom {M N : NondegenerateModuleCat.{uA, v} A} (f : M ⟶ N) :
    ((P hB hBA hnd).map f).hom.toAddMonoidHom =
      NonUnitalModuleTensor.map A (NonUnitalModuleHom.id Aᵐᵒᵖ B) f.hom := rfl

theorem P_map_tmul {M N : NondegenerateModuleCat.{uA, v} A}
    (f : M ⟶ N) (b : B) (m : M.obj) :
    ((P hB hBA hnd).map f).hom.toAddMonoidHom (tmul A B M.obj b m) =
      tmul A B N.obj b (f.hom.toAddMonoidHom m) := rfl

end P

section RegularF

variable [NonUnitalModule A B]

/-- Source F with exactly the published right regular B-action. -/
def regularF (hA : IsIdempotented A) (hB : IsIdempotented B)
    (hAB : @ActionsCommute A B B _ _ _ _ (NonUnitalModule.rightRegular B))
    (hLeft : IsNondegenerate A B) :
    NondegenerateModuleCat.{uB, v} B ⥤ NondegenerateModuleCat.{uA, max uB v} A :=
  @F A B _ _ _ (NonUnitalModule.rightRegular B) hA hAB
    ⟨hLeft, rightRegular_isNondegenerate hB⟩

instance regularF_additive (hA : IsIdempotented A) (hB : IsIdempotented B)
    (hAB : @ActionsCommute A B B _ _ _ _ (NonUnitalModule.rightRegular B))
    (hLeft : IsNondegenerate A B) : (regularF.{uA, uB, v} hA hB hAB hLeft).Additive :=
  @F_additive A B _ _ _ (NonUnitalModule.rightRegular B) hA hAB
    ⟨hLeft, rightRegular_isNondegenerate hB⟩

theorem regularF_eq_restrictedFunctor (hA : IsIdempotented A) (hB : IsIdempotented B)
    (hAB : @ActionsCommute A B B _ _ _ _ (NonUnitalModule.rightRegular B))
    (hLeft : IsNondegenerate A B) :
    regularF.{uA, uB, v} hA hB hAB hLeft =
      @restrictedFunctor A B _ _ B _ _ (NonUnitalModule.rightRegular B) hA hAB hLeft := rfl

attribute [local instance] NonUnitalModule.rightRegular

variable (hA : IsIdempotented A) (hB : IsIdempotented B)
  (hAB : @ActionsCommute A B B _ _ _ _ (NonUnitalModule.rightRegular B))
  (hLeft : IsNondegenerate A B)

theorem regularF_obj (N : NondegenerateModuleCat.{uB, v} B) :
    ((regularF hA hB hAB hLeft).obj N).obj = tensorObj hAB N.obj := rfl

theorem regularF_obj_carrier (N : NondegenerateModuleCat.{uB, v} B) :
    ((regularF hA hB hAB hLeft).obj N).obj.carrier = Tensor B B N.obj := rfl

theorem regularF_obj_addCommGroup (N : NondegenerateModuleCat.{uB, v} B) :
    ((regularF hA hB hAB hLeft).obj N).obj.isAddCommGroup =
      NonUnitalModuleTensor.addCommGroup B B N.obj := rfl

theorem regularF_obj_module (N : NondegenerateModuleCat.{uB, v} B) :
    ((regularF hA hB hAB hLeft).obj N).obj.isModule =
      NonUnitalBimoduleTensor.leftModule hAB N.obj := rfl

theorem regularF_map_hom {M N : NondegenerateModuleCat.{uB, v} B} (f : M ⟶ N) :
    ((regularF hA hB hAB hLeft).map f).hom =
      NonUnitalBimoduleTensor.leftMap hAB hAB (NonUnitalBimoduleHom.id A B B) f.hom := rfl

theorem regularF_map_toAddMonoidHom {M N : NondegenerateModuleCat.{uB, v} B} (f : M ⟶ N) :
    ((regularF hA hB hAB hLeft).map f).hom.toAddMonoidHom =
      NonUnitalModuleTensor.map B (NonUnitalModuleHom.id Bᵐᵒᵖ B) f.hom := rfl

theorem regularF_map_tmul {M N : NondegenerateModuleCat.{uB, v} B}
    (f : M ⟶ N) (b : B) (m : M.obj) :
    ((regularF hA hB hAB hLeft).map f).hom.toAddMonoidHom (tmul B B M.obj b m) =
      tmul B B N.obj b (f.hom.toAddMonoidHom m) := rfl

end RegularF

section RegularP

variable [NonUnitalModule Aᵐᵒᵖ B]

/-- Source P with exactly the published left regular B-action. -/
def regularP (hB : IsIdempotented B)
    (hBA : @ActionsCommute B A B _ _ _ (NonUnitalModule.regular B) _)
    (hRight : IsRightNondegenerate A B) :
    NondegenerateModuleCat.{uA, v} A ⥤ NondegenerateModuleCat.{uB, max uB v} B :=
  @P A B _ _ (NonUnitalModule.regular B) _ hB hBA
    ⟨regular_isNondegenerate hB, hRight⟩

instance regularP_additive (hB : IsIdempotented B)
    (hBA : @ActionsCommute B A B _ _ _ (NonUnitalModule.regular B) _)
    (hRight : IsRightNondegenerate A B) : (regularP.{uA, uB, v} hB hBA hRight).Additive :=
  @P_additive A B _ _ (NonUnitalModule.regular B) _ hB hBA
    ⟨regular_isNondegenerate hB, hRight⟩

theorem regularP_eq_restrictedFunctor (hB : IsIdempotented B)
    (hBA : @ActionsCommute B A B _ _ _ (NonUnitalModule.regular B) _)
    (hRight : IsRightNondegenerate A B) :
    regularP.{uA, uB, v} hB hBA hRight =
      @restrictedFunctor B A _ _ B _ (NonUnitalModule.regular B) _ hB hBA
        (regular_isNondegenerate hB) := rfl

attribute [local instance] NonUnitalModule.regular

variable (hB : IsIdempotented B)
  (hBA : @ActionsCommute B A B _ _ _ (NonUnitalModule.regular B) _)
  (hRight : IsRightNondegenerate A B)

theorem regularP_obj (M : NondegenerateModuleCat.{uA, v} A) :
    ((regularP hB hBA hRight).obj M).obj = tensorObj hBA M.obj := rfl

theorem regularP_obj_carrier (M : NondegenerateModuleCat.{uA, v} A) :
    ((regularP hB hBA hRight).obj M).obj.carrier = Tensor A B M.obj := rfl

theorem regularP_obj_addCommGroup (M : NondegenerateModuleCat.{uA, v} A) :
    ((regularP hB hBA hRight).obj M).obj.isAddCommGroup =
      NonUnitalModuleTensor.addCommGroup A B M.obj := rfl

theorem regularP_obj_module (M : NondegenerateModuleCat.{uA, v} A) :
    ((regularP hB hBA hRight).obj M).obj.isModule =
      NonUnitalBimoduleTensor.leftModule hBA M.obj := rfl

theorem regularP_map_hom {M N : NondegenerateModuleCat.{uA, v} A} (f : M ⟶ N) :
    ((regularP hB hBA hRight).map f).hom =
      NonUnitalBimoduleTensor.leftMap hBA hBA (NonUnitalBimoduleHom.id B A B) f.hom := rfl

theorem regularP_map_toAddMonoidHom {M N : NondegenerateModuleCat.{uA, v} A} (f : M ⟶ N) :
    ((regularP hB hBA hRight).map f).hom.toAddMonoidHom =
      NonUnitalModuleTensor.map A (NonUnitalModuleHom.id Aᵐᵒᵖ B) f.hom := rfl

theorem regularP_map_tmul {M N : NondegenerateModuleCat.{uA, v} A}
    (f : M ⟶ N) (b : B) (m : M.obj) :
    ((regularP hB hBA hRight).map f).hom.toAddMonoidHom (tmul A B M.obj b m) =
      tmul A B N.obj b (f.hom.toAddMonoidHom m) := rfl

end RegularP

end Source

end Langlands.Algebra.NondegenerateTensorFunctor
