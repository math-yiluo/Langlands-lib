/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Geometry.SemilinearGeometryOps
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricOperationsBaseExistence
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricOperationsTransitionExistence

/-! # Normalized geometric operations on semilinear systems

Source: Zheng Construction 4.1 and Lemma 4.10. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe c v r
open CategoryTheory CategoryTheory.Limits
namespace WeilConjectures.SemilinearSections
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

/-- Normalized geometric operations on semilinear systems.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 06YY, 07A4, 07A6.
(blueprint: lem-coef-semilinear-geometric-operations).

Proof: Apply $u^{-1}$ and $u_*$ termwise on the underlying sequence topoi. Their adjunction
follows by applying the original adjunction at every index: the naturality equations for a family
of maps correspond under transposition. The inverse image preserves finite limits and colimits, so
is exact on module systems, with coefficient ring $C_\bullet=u^{-1}B_\bullet$. This is a morphism
of the two ringed sequence topoi. Apply [lem-weil-pbc-ringed-projection-mate-exact] and
[prop-pur-kinjective-resolutions-exist] there. They give $V\dashv G=Ru_{*,\bullet}$, with $G$
computed by a K-injective system resolution and $V$ termwise exact. The unit and counit here are
maps in the ordinary derived categories of systems.

Write $L_n^B,L_n^C$ for the finite left extensions on the two sites. On a flat-term K-flat
representative $P$, inverse image and coefficient tensor give $VE_n^BP\cong E_n^Cu^{-1}P$, with
the same zero components above $n$. The isomorphism is $u^{-1}(P\otimes_{B_n}B_q)\cong
u^{-1}P\otimes_{C_n}C_q$. K-flat pullback and derived tensor/pullback identify it as $VL_n^B\cong
L_n^Cu^{-1}$ on the ordinary derived categories. For $P\in D(B_n)$ and $N\in D(\mathscr S(C))$,
the natural bijections
Hom(P,e_nGN) ≅ Hom(L_n^B P,GN) ≅ Hom(V L_n^B P,N)
≅ Hom(L_n^C u⁻¹P,N) ≅ Hom(u⁻¹P,N_n) ≅ Hom(P,Ru_{*,n}N_n)
therefore give $e_nG\cong Ru_{*,n}e_n$ by Yoneda. This proves the formula without any preservation
of K-injectives by evaluation.

Use the canonical adjunctions in the preceding Hom bijections. The derived adjunction formula on a
resolving representative is the ordinary tensor-adjoint formula: its unit sends $x$ to
$x\otimes1$, and its transpose sends $x\otimes a$ to $a h(x)$. This follows from the canonical
pre-derived adjunction formula of [lem-pc-pre-derived-adjoint-functors-general], with the identity
resolving leg, and then naturality in a K-flat resolution. Consequently the Hom bijections
defining $e_nG$ carry the evaluated unit and counit to the level unit and counit: applying the
bijection to an identity gives its unit, and applying its inverse to an identity gives its counit.
The comparison $VL_n^B\cong L_n^Cu^{-1}$ commutes with $\sigma_{mn}$, since its two composites are
the same inverse-image tensor reassociation on $q\leq n$ and zero above. Transpose this square.
The reduction transition of $GN$ becomes $G_n(t^N_{m,n})b_{m,n}$, where $b$ is the transpose of
$$u^{-1}T_{m,n}G_m\xrightarrow{q^{-1}}S_{m,n}u^{-1}G_m\xrightarrow{S_{m,n}\varepsilon_m}S_{m,n}.$$
Ordinary mate pasting gives the composition law. This proves compatibility of evaluations with the
adjunction maps and coefficient transitions, not merely the evaluated objects.

For geometric tensor pullback use the inverse-image pure-tensor comparison on each total-complex
summand, with the inverse ordinary comparison as its recorded inverse. The differential signs make
these chain maps. Resolving on the system site by K-flat complexes with flat terms gives the
normalized derived comparison; hence its specification is checked before evaluation, without
assuming derived evaluation is faithful. -/
theorem semilinearGeometricOperations (systems : Data.{c, v, r} J B τ)
    {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
    (J' : GrothendieckTopology C')
    (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
    (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (adjSet : uInv ⊣ uPush) [PreservesFiniteLimits uInv] :
    Nonempty {G : Geometry.{c, v, r} J B τ systems J' uInv uPush adjSet //
      G.PullTransitionFormula J B τ systems J' uInv uPush adjSet} := by
  obtain ⟨G⟩ := semilinearGeometryBaseExistence J B τ systems J' uInv uPush adjSet
  exact ⟨⟨G, semilinearGeometryTransitionExistence J B τ systems J' uInv uPush adjSet G⟩⟩

end WeilConjectures.SemilinearSections
