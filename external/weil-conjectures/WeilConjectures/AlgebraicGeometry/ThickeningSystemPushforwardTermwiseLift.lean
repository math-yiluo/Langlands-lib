/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ThickeningSystemPushforward
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPowerQuotient
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardIdealPowers
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardFullyFaithful

@[expose] public section
universe v
open CategoryTheory Opposite
namespace AlgebraicGeometry
noncomputable section
set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false in
/-- A lifted adjacent transition becomes invertible after tensor pullback.
Source: Stacks, Remark 088F, Lemma 087T and equation 0880.
(blueprint: lem-weil-pbc-thickening-system-pushforward-lifting-termwise).

Proof: The morphism i_n is a closed immersion because its composite with j_(n+1)
is the closed immersion j_n and j_(n+1) is a monomorphism. Its kernel is the
pullback of J^(n+1) along j_(n+1). The unit quotient theorem identifies
pushforward of i_n^* G with G modulo this kernel. The ideal-power pushforward
comparison identifies its further pushforward with the quotient of H_(n+1)
by J^(n+1), using eG. The displayed transition equation and the adjunction
identity say that the pushforward of the adjoint of u is the map induced by
the transition of H on that quotient, followed by eF.inv. The adic condition
on H says that this induced map is invertible. Finally the fully faithful
closed pushforward j_n reflects isomorphisms, so the adjoint of u is invertible.
This is a single adjacent quotient comparison, with both coherent terms and
u supplied as inputs; it asserts no existence of an inverse system. -/
theorem thickeningSystemPushforward_adjacent_isIso
    {X : Scheme.{v}} [IsNoetherian X] {T : ℕ → Scheme.{v}}
    {i : ∀ n, T n ⟶ T (n + 1)}
    (j : ∀ n, T n ⟶ X) (hi : ∀ n, i n ≫ j (n + 1) = j n)
    (ai : ∀ n, Scheme.Modules.tensorPullback (i n) ⊣ Scheme.Modules.pushforward (i n))
    (J : X.IdealSheafData)
    (hgeom : ∀ n, IsClosedImmersion (j n) ∧ (j n).ker = J ^ (n + 1))
    (H : CoherentFormalModule X J) (n : ℕ)
    (F : (T n).Modules) (G : (T (n + 1)).Modules)
    (hF : RingedSpace.IsCoherent (T n).toRingedSpace F)
    (hG : RingedSpace.IsCoherent (T (n + 1)).toRingedSpace G)
    (eF : (Scheme.Modules.pushforward (j n)).obj F ≅ H.obj.obj (op n))
    (eG : (Scheme.Modules.pushforward (j (n + 1))).obj G ≅ H.obj.obj (op (n + 1)))
    (u : G ⟶ (Scheme.Modules.pushforward (i n)).obj F)
    (hu : (Scheme.Modules.pushforward (j (n + 1))).map u ≫
        (thickeningPushforwardComparison j hi n).hom.app F ≫ eF.hom =
      eG.hom ≫ H.obj.map (homOfLE (Nat.le_succ n)).op) :
    IsIso ((ai n).homEquiv G F |>.symm u) := by
  classical
  have _ := hF
  have hj (k : ℕ) : IsClosedImmersion (j k) := (hgeom k).1
  have hicomp : IsClosedImmersion (i n ≫ j (n + 1)) := hi n ▸ hj n
  have : IsClosedImmersion (i n) :=
    IsClosedImmersion.of_comp_isClosedImmersion (i n) (j (n + 1))
  have : IsLocallyNoetherian (T (n + 1)) :=
    LocallyOfFiniteType.isLocallyNoetherian (j (n + 1))
  have : G.IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType (T (n + 1)) G).mp hG).1
  have hk : (i n).ker = (J.comap (j (n + 1))) ^ (n + 1) := by
    rw [← Scheme.IdealSheafData.comap_map_of_isClosedImmersion (j (n + 1)) (i n).ker,
      Scheme.IdealSheafData.map_ker, hi n, (hgeom n).2,
      Scheme.IdealSheafData.comap_pow]
  obtain ⟨q, hq⟩ := closedImmersion_power_quotient (J.comap (j (n + 1)))
    (n + 1) (i n) hk (ai n) G
  obtain ⟨ρ, hρ, _, _⟩ :=
    (Scheme.closedImmersion_pushforward_idealPowers (j (n + 1)) J).2.2.2
  let d := ρ G (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) ≪≫
    (Scheme.Modules.pushforward (j (n + 1))).mapIso q ≪≫
    (thickeningPushforwardComparison j hi n).app ((Scheme.Modules.tensorPullback (i n)).obj G)
  have hd : formalModuleQuotientπ J (n + 1)
      ((Scheme.Modules.pushforward (j (n + 1))).obj G) ≫ d.hom =
      (Scheme.Modules.pushforward (j (n + 1))).map ((ai n).unit.app G) ≫
        (thickeningPushforwardComparison j hi n).hom.app
          ((Scheme.Modules.tensorPullback (i n)).obj G) := by
    dsimp only [d, Iso.trans_hom, Functor.mapIso_hom]
    rw [← Category.assoc, ← Category.assoc, hρ G (n + 1) (Nat.succ_le_succ (Nat.zero_le n)),
      ← Functor.map_comp, hq]
    rfl
  let e : formalModuleQuotient J (n + 1)
      ((Scheme.Modules.pushforward (j (n + 1))).obj G) ≅
      formalModuleQuotient J (n + 1) (H.obj.obj (op (n + 1))) :=
    { hom := formalModuleQuotientMap J eG.hom (Nat.le_refl (n + 1))
      inv := formalModuleQuotientMap J eG.inv (Nat.le_refl (n + 1))
      hom_inv_id := by
        rw [← formalModuleQuotientMap_comp, eG.hom_inv_id]
        exact formalModuleQuotientMap_id J _ _
      inv_hom_id := by
        rw [← formalModuleQuotientMap_comp, eG.inv_hom_id]
        exact formalModuleQuotientMap_id J _ _ }
  obtain ⟨a, ha⟩ := H.property.2.2 n
  let f := (ai n).homEquiv G F |>.symm u
  have hf : (ai n).unit.app G ≫ (Scheme.Modules.pushforward (i n)).map f = u := by
    rw [← (ai n).homEquiv_unit G F f]
    exact (ai n).homEquiv G F |>.apply_symm_apply u
  have he : d.hom ≫ (Scheme.Modules.pushforward (j n)).map f ≫ eF.hom =
      e.hom ≫ a.hom := by
    apply (cancel_epi (CategoryTheory.Limits.cokernel.π (Scheme.idealModuleProductι
      (Scheme.idealSheafPower J.toModulesι (n + 1)).2
        ((Scheme.Modules.pushforward (j (n + 1))).obj G)))).1
    change formalModuleQuotientπ J (n + 1) _ ≫ _ = _
    rw [← Category.assoc, ← Category.assoc, hd]
    simp only [Category.assoc]
    rw [← NatTrans.naturality_assoc]
    simp only [Functor.comp_map, ← Category.assoc, ← Functor.map_comp]
    rw [hf]
    simp only [Category.assoc]
    rw [hu]
    change _ = (formalModuleQuotientπ J (n + 1) _ ≫
      formalModuleQuotientMap J eG.hom (Nat.le_refl (n + 1))) ≫ a.hom
    simp only [formalModuleQuotientπ, formalModuleQuotientMap,
      CategoryTheory.Limits.cokernel.π_desc, Category.assoc]
    exact congrArg (eG.hom ≫ ·) ha.symm
  have hm : (Scheme.Modules.pushforward (j n)).map f =
      d.inv ≫ e.hom ≫ a.hom ≫ eF.inv := by
    calc
      _ = d.inv ≫ (d.hom ≫ (Scheme.Modules.pushforward (j n)).map f ≫ eF.hom) ≫
          eF.inv := by simp
      _ = _ := by rw [he]; simp only [Category.assoc]
  have : IsIso ((Scheme.Modules.pushforward (j n)).map f) := by
    rw [hm]
    exact (d.symm ≪≫ e ≪≫ a ≪≫ eF.symm).isIso_hom
  let hff := (closedImmersion_pushforward_fullyFaithful (j n)).2
  let : (Scheme.Modules.pushforward (j n)).Full :=
    { map_surjective := fun {X Y} ↦ (hff X Y).2 }
  let : (Scheme.Modules.pushforward (j n)).Faithful :=
    { map_injective := fun {X Y} ↦ (hff X Y).1 }
  exact isIso_of_reflects_iso f (Scheme.Modules.pushforward (j n))

end
end AlgebraicGeometry
