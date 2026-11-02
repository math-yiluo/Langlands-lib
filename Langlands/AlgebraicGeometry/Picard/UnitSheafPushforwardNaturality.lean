import Langlands.AlgebraicGeometry.Picard.UnitSheafPushforward
import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences

/-! # Normalization and naturality of actual sheaf cohomology pushforward -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace

namespace Langlands.AlgebraicGeometry.Picard.UnitSheafPushforward

set_option backward.isDefEq.respectTransparency false

private lemma homEquiv_uniq_inv_comp
    {C D : Type*} [Category* C] [Category* D]
    {L L' : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) (b : L' ⊣ R)
    {A : C} {B : D} (f : L.obj A ⟶ B) :
    b.homEquiv _ _ ((a.leftAdjointUniq b).inv.app A ≫ f) =
      a.homEquiv _ _ f := by
  simp only [Adjunction.leftAdjointUniq_inv_app, Adjunction.homEquiv_unit,
    Functor.map_comp, ← Category.assoc, Adjunction.unit_leftAdjointUniq_hom_app]

variable {X Y : TopCat.{u}} (e : X ≅ Y)

private abbrev pushforwardAdjunction :
    TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.inv ⊣
      TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom :=
  (sheafPushforwardEquivalence (C := AddCommGrpCat.{u}) e).symm.toAdjunction

local instance :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).IsEquivalence :=
  (sheafPushforwardEquivalence (C := AddCommGrpCat.{u}) e).isEquivalence_functor

local instance :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.inv).IsEquivalence :=
  (sheafPushforwardEquivalence (C := AddCommGrpCat.{u}) e).isEquivalence_inverse

local instance :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).Additive :=
  Functor.additive_of_preserves_binary_products _

local instance :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.inv).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- A formula in the existing Ext groups for the published pushforward equivalence. -/
lemma cohomologyPushforwardEquiv_apply (F : X.Sheaf AddCommGrpCat.{u}) (n : ℕ)
    (x : Sheaf.H.{u}
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).obj F) n) :
    cohomologyPushforwardEquiv e F n x =
      (Ext.mk₀ ((constantInversePushforwardIso e).inv.app
        (AddCommGrpCat.of (ULift ℤ)))).comp
          ((pushforwardAdjunction e).extEquiv.symm
            x) (zero_add n) := rfl

/-- The published equivalence commutes with actual coefficient maps in every degree. -/
lemma cohomologyPushforwardEquiv_naturality
    {F G : X.Sheaf AddCommGrpCat.{u}} (φ : F ⟶ G) (n : ℕ)
    (x : Sheaf.H.{u}
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).obj F) n) :
    cohomologyPushforwardEquiv e G n
        (Sheaf.H.map ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).map φ) n x) =
      Sheaf.H.map φ n (cohomologyPushforwardEquiv e F n x) := by
  rw [cohomologyPushforwardEquiv_apply, cohomologyPushforwardEquiv_apply,
    Sheaf.H.map_apply, Sheaf.H.map_apply,
    Adjunction.extEquiv_symm_naturality_right₀, Ext.comp_assoc]
  lia

/-- Pushforward along the homeomorphism preserves the actual connecting homomorphisms. -/
lemma cohomologyPushforwardEquiv_δ
    {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})} (hS : S.ShortExact)
    (n m : ℕ) (h : n + 1 = m)
    (x : Sheaf.H.{u}
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).obj S.X₃) n) :
    cohomologyPushforwardEquiv e S.X₁ m
        (Sheaf.H.δ (hS.map_of_exact
          (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom)) n m h x) =
      Sheaf.H.δ hS n m h (cohomologyPushforwardEquiv e S.X₃ n x) := by
  rw [cohomologyPushforwardEquiv_apply, cohomologyPushforwardEquiv_apply]
  change (Ext.mk₀ _).comp
      ((pushforwardAdjunction e).extEquiv.symm
          (x.comp (hS.map_of_exact
            (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom)).extClass h))
      (zero_add m) =
    ((Ext.mk₀ _).comp _ (zero_add n)).comp hS.extClass h
  rw [← Ext.mapExactFunctor_extClass,
    Adjunction.extEquiv_symm_naturality_right, Ext.comp_assoc]
  lia

/-- In degree zero the published equivalence is the identity on global sections. -/
lemma cohomologyPushforwardEquiv_equiv₀ (F : X.Sheaf AddCommGrpCat.{u})
    (x : Sheaf.H.{u}
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).obj F) 0) :
    Sheaf.H.equiv₀ F (isTerminalTop (α := Opens X))
        (cohomologyPushforwardEquiv e F 0 x) =
      Sheaf.H.equiv₀
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).obj F)
        (isTerminalTop (α := Opens Y)) x := by
  obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective
    ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift ℤ)))
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).obj F)).2 x
  rw [cohomologyPushforwardEquiv_apply, Adjunction.extEquiv_symm_mk₀,
    Ext.mk₀_comp_mk₀]
  simp only [Sheaf.H.equiv₀, AddEquiv.trans_apply, ← Ext.addEquiv₀_symm_apply,
    AddEquiv.apply_symm_apply, Adjunction.homAddEquiv_apply]
  change (AddCommGrpCat.uliftZMultiplesAddEquiv _)
      ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
        (isTerminalTop (α := Opens X))).homEquiv _ _
          ((constantInversePushforwardIso e).inv.app (AddCommGrpCat.of (ULift ℤ)) ≫
            ((sheafPushforwardEquivalence (C := AddCommGrpCat.{u}) e).symm.toAdjunction.homEquiv _ _).symm f)) =
    (AddCommGrpCat.uliftZMultiplesAddEquiv _)
      ((constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
        (isTerminalTop (α := Opens Y))).homEquiv _ _ f)
  apply congrArg (AddCommGrpCat.uliftZMultiplesAddEquiv _)
  have hh := homEquiv_uniq_inv_comp
        ((constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
          (isTerminalTop (α := Opens Y))).comp
            (sheafPushforwardEquivalence (C := AddCommGrpCat.{u}) e).symm.toAdjunction)
        (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
          (isTerminalTop (α := Opens X)))
        (((sheafPushforwardEquivalence (C := AddCommGrpCat.{u}) e).symm.toAdjunction.homEquiv _ _).symm f)
  rw [Adjunction.comp_homEquiv] at hh
  change (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
      (isTerminalTop (α := Opens X))).homEquiv _ _
        ((constantInversePushforwardIso e).inv.app (AddCommGrpCat.of (ULift ℤ)) ≫
          ((sheafPushforwardEquivalence (C := AddCommGrpCat.{u}) e).symm.toAdjunction.homEquiv
            _ _).symm f) =
    (constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
      (isTerminalTop (α := Opens Y))).homEquiv _ _
        ((sheafPushforwardEquivalence (C := AddCommGrpCat.{u}) e).symm.toAdjunction.homEquiv
          _ _ (((sheafPushforwardEquivalence (C := AddCommGrpCat.{u}) e).symm.toAdjunction.homEquiv _ _).symm f)) at hh
  simpa only [Equiv.apply_symm_apply, sheafPushforwardEquivalence,
    CategoryTheory.Equivalence.symm, CategoryTheory.Equivalence.mk] using hh

/-- The degree-zero identification also commutes in the section-to-cohomology direction. -/
lemma cohomologyPushforwardEquiv_equiv₀_symm (F : X.Sheaf AddCommGrpCat.{u})
    (s : F.obj.obj (op ⊤)) :
    cohomologyPushforwardEquiv e F 0
        ((Sheaf.H.equiv₀
          ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).obj F)
          (isTerminalTop (α := Opens Y))).symm s) =
      (Sheaf.H.equiv₀ F (isTerminalTop (α := Opens X))).symm s := by
  apply (Sheaf.H.equiv₀ F (isTerminalTop (α := Opens X))).injective
  rw [cohomologyPushforwardEquiv_equiv₀,
    AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/-- The published equivalences form a natural isomorphism of actual cohomology functors. -/
def cohomologyPushforwardNatIso (n : ℕ) :
    TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom ⋙
        Sheaf.functorH.{u} (Opens.grothendieckTopology Y) n ≅
      Sheaf.functorH.{u} (Opens.grothendieckTopology X) n :=
  NatIso.ofComponents (fun F => (cohomologyPushforwardEquiv e F n).toAddCommGrpIso)
    (by
      intro F G φ
      ext x
      exact cohomologyPushforwardEquiv_naturality e φ n x)

@[simp]
lemma cohomologyPushforwardNatIso_hom_app (F : X.Sheaf AddCommGrpCat.{u}) (n : ℕ)
    (x : Sheaf.H.{u}
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).obj F) n) :
    (cohomologyPushforwardNatIso e n).hom.app F x =
      cohomologyPushforwardEquiv e F n x := rfl

end Langlands.AlgebraicGeometry.Picard.UnitSheafPushforward
