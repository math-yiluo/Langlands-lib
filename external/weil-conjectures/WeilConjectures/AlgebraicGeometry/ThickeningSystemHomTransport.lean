/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentThickeningSystem
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardFullyFaithful
import WeilConjectures.AlgebraicGeometry.ThickeningSystemHomTransportCore
import WeilConjectures.AlgebraicGeometry.ThickeningSystemComparisonTransport
import WeilConjectures.AlgebraicGeometry.TensorPullback

/-! # Transport of compatible morphism families

Source: Stacks Project, Remark 088F and Lemma 087T.
(blueprint: lem-weil-pbc-thickening-system-hom-transport).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Evaluation comparisons transport system arrows to restriction families, independently
of the natural pullback comparison chosen. This concerns a restriction functor only;
it makes no assertion about formal completions or an equivalence of categories.
Source: Stacks Project, Remark 088F and Lemma 087T.
(blueprint: lem-weil-pbc-thickening-system-hom-transport).

Proof: First use d as the comparison. Send a system arrow a to the family
(r_n,G).inv followed by a.app n followed by (r_n,F).hom. In the reverse direction,
conjugate each v_n by (r_n,G).hom and (r_n,F).inv. Substitute the displayed equation
hr for G and F into the system compatibility equation, use functoriality of pullback,
and cancel the r isomorphisms. This proves compatibility in both directions.
The two conjugations are inverse componentwise, and the compatibility proofs are
irrelevant, so this gives an equivalence of sets.

To replace d by c, their difference d_n.symm followed by c_n is a natural
automorphism alpha of j_n^*. For L=j_n^* and its right adjoint U=j_n,*, the counit
is invertible by 087T. Its triangle identity makes L(unit_M) invertible. Define
beta_N on N by conjugating alpha_(U N) by the counit at N. Counit naturality and
alpha naturality make beta natural in every map N to N'. Naturality of alpha at
the unit of M and the triangle identity give beta_(L M)=alpha_M. Thus alpha_G
commutes with every v_n:L G to L F, even when v_n does not lift to X. Substitute
c_n=d_n followed by alpha into its compatibility equation and cancel alpha_F;
the c and d equations are equivalent. This identifies the two family subtypes
without changing their components. Finally naturality of r shows that the family
attached to R.map w has components j_n^*w. Naturality of c supplies its subtype
proof. The argument also applies to empty schemes and zero modules. -/
theorem thickeningSystem_hom_transport
    {X : Scheme.{u}} {T : ℕ → Scheme.{u}} {i : ∀ n, T n ⟶ T (n + 1)}
    (j : ∀ n, T n ⟶ X) (hj : ∀ n, IsClosedImmersion (j n))
    (c d : ∀ n, Scheme.Modules.tensorPullback (j (n + 1)) ⋙
      Scheme.Modules.tensorPullback (i n) ≅ Scheme.Modules.tensorPullback (j n))
    (R : CoherentModules X ⥤ CoherentThickeningSystem T i)
    (r : ∀ n, R ⋙ CoherentThickeningSystem.evaluation T i n ≅
      ObjectProperty.ι (RingedSpace.IsCoherent X.toRingedSpace) ⋙
        Scheme.Modules.tensorPullback (j n))
    (hr : ∀ (F : CoherentModules X) (n : ℕ),
      ((R.obj F).comparison n).hom ≫ (r n).hom.app F =
        (Scheme.Modules.tensorPullback (i n)).map ((r (n + 1)).hom.app F) ≫
          (d n).hom.app F.obj)
    (F G : CoherentModules X) :
    ∃ e : (R.obj G ⟶ R.obj F) ≃
      {v : ∀ n, (Scheme.Modules.tensorPullback (j n)).obj G.obj ⟶
        (Scheme.Modules.tensorPullback (j n)).obj F.obj |
        ∀ n, (c n).hom.app G.obj ≫ v n =
          (Scheme.Modules.tensorPullback (i n)).map (v (n + 1)) ≫ (c n).hom.app F.obj},
      ∀ w : G ⟶ F, e (R.map w) =
        ⟨fun n ↦ (Scheme.Modules.tensorPullback (j n)).map w.hom,
          fun n ↦ ((c n).hom.naturality w.hom).symm⟩ := by
  obtain ⟨ed, hed⟩ := thickeningSystem_hom_transport_d j d R r hr F G
  obtain ⟨ec, hec⟩ := compatible_family_comparison_equiv j hj c d F G
  refine ⟨ed.trans ec, ?_⟩
  intro w
  apply Subtype.ext
  change (ec (ed (R.map w))).val = _
  rw [hec, hed]

end AlgebraicGeometry
