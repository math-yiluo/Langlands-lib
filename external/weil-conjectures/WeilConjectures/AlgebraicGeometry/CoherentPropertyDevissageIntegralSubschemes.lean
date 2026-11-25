/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Preadditive.Biproducts
import WeilConjectures.AlgebraicGeometry.CoherentPropertyIntegralIdealsOfSmallSupport
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks
import WeilConjectures.AlgebraicGeometry.CoherentFiltrationIntegralSubschemes
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import WeilConjectures.AlgebraicGeometry.IntegralIdealGenericStalk

/-!
# Devissage of a property of coherent modules

Source: literature/stacks-project/coherent.tex, Lemma 01YM
(blueprint: lem-weil-pbc-coherent-property-devissage-integral-subschemes).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits ZeroObject
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

private theorem ft_iso {X : Scheme.{u}} {F G : X.Modules} (e : F ≅ G)
    (hF : F.IsFiniteType) : G.IsFiniteType := by
  have := hF
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData F
  let q' : G.LocalGeneratorsData :=
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      generators j := (q.generators j).ofEpi
        ((SheafOfModules.overFunctor X.ringCatSheaf (q.X j)).map e.hom) }
  refine { exists_localGeneratorsData := ⟨q', ?_⟩ }
  constructor
  intro j
  have := hq.isFiniteType j
  exact inferInstanceAs ((q.generators j).ofEpi
    ((SheafOfModules.overFunctor X.ringCatSheaf (q.X j)).map e.hom)).IsFiniteType
private theorem coh_iso {X : Scheme.{u}} [IsLocallyNoetherian X] {F G : X.Modules}
    (e : F ≅ G) (hF : RingedSpace.IsCoherent X.toRingedSpace F) :
    RingedSpace.IsCoherent X.toRingedSpace G := by
  obtain ⟨hq, ht⟩ := (isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mp hF
  exact (isCoherent_iff_isQuasicoherent_and_isFiniteType X G).mpr
    ⟨(SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e hq, ft_iso e ht⟩
private theorem coh_zero {X : Scheme.{u}} [IsLocallyNoetherian X]
    {F : X.Modules} (hF : RingedSpace.IsCoherent X.toRingedSpace F) :
    RingedSpace.IsCoherent X.toRingedSpace (0 : X.Modules) := by
  have hk := ((isCoherent_kernel_cokernel_biprod_and_submodule X).1 F F hF hF).1 (𝟙 F)
  exact coh_iso (isZero_kernel_of_mono (𝟙 F)).isoZero hk.1
private theorem p_iso {X : Scheme.{u}} [IsLocallyNoetherian X]
    (P : X.Modules → Prop) (hz : P (0 : X.Modules))
    (he : ∀ (S : ShortComplex X.Modules), S.ShortExact →
      RingedSpace.IsCoherent X.toRingedSpace S.X₁ →
      RingedSpace.IsCoherent X.toRingedSpace S.X₂ →
      RingedSpace.IsCoherent X.toRingedSpace S.X₃ →
      P S.X₁ → P S.X₃ → P S.X₂)
    {F G : X.Modules} (e : F ≅ G) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hG : P G) : P F := by
  let S : ShortComplex X.Modules := ShortComplex.mk (0 : 0 ⟶ F) e.hom (by simp)
  have hs : S.ShortExact :=
    { exact := (S.exact_iff_mono rfl).mpr inferInstance }
  exact he S hs (coh_zero hF) hF (coh_iso e hF) hz hG

private theorem stalk_inj {X : Scheme.{u}} {F G : X.Modules} (f : F ⟶ G) [Mono f]
    (x : X) : Function.Injective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map f).hom := by
  have hm := (RingedSpace.module_stalk_exact X.toRingedSpace f).1
    (fun U ↦ by
      apply (ModuleCat.mono_iff_injective _).mp
      exact Functor.map_mono (SheafOfModules.evaluation X.ringCatSheaf (Opposite.op U)) f) x
  exact (ModuleCat.mono_iff_injective _).mp hm
private theorem support_mono {X : Scheme.{u}} {F G : X.Modules} (f : F ⟶ G) [Mono f] :
    {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ⊆
      {x : X | ¬ Subsingleton (G.presheaf.stalk x)} := by
  intro x hx hg
  have : Subsingleton ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj G) := hg
  exact hx (Function.Injective.subsingleton (stalk_inj f x))
private theorem support_cokernel {X : Scheme.{u}} {F G : X.Modules} (f : F ⟶ G) :
    {x : X | ¬ Subsingleton ((cokernel f).presheaf.stalk x)} ⊆
      {x : X | ¬ Subsingleton (G.presheaf.stalk x)} := by
  intro x hx hg
  have he := (RingedSpace.module_stalk_exact X.toRingedSpace f).2.2.1 x
  have : Subsingleton ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj G) := hg
  exact hx (Function.Surjective.subsingleton
    ((ModuleCat.epi_iff_surjective _).mp he.1))
private theorem support_iso {X : Scheme.{u}} {F G : X.Modules} (e : F ≅ G) :
    {x : X | ¬ Subsingleton (F.presheaf.stalk x)} =
      {x : X | ¬ Subsingleton (G.presheaf.stalk x)} := by
  exact Set.Subset.antisymm (support_mono e.hom) (support_mono e.inv)
private theorem support_integral_ideal {X Z : Scheme.{u}} [IsLocallyNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (I : Z.IdealSheafData) (hI : I ≠ ⊥)
    (hF : RingedSpace.IsCoherent X.toRingedSpace ((pushforward i).obj I.toModules)) :
    {x : X | ¬ Subsingleton (((pushforward i).obj I.toModules).presheaf.stalk x)} =
      Set.range i.base := by
  let F := (pushforward i).obj I.toModules
  obtain ⟨hq, ht⟩ := (isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mp hF
  have := hq
  have := ht
  have hclosed := (finite_type_module_support_closed X F).2.2.2
  have hstalk := closedImmersion_pushforward_stalks i i.isClosedEmbedding I.toModules
  have hgeneric : i.base (genericPoint Z) ∈
      {x : X | ¬ Subsingleton (F.presheaf.stalk x)} := by
    intro hzero
    have : Subsingleton (F.presheaf.stalk (i.base (genericPoint Z))) := hzero
    have hn := (integral_ideal_generic_stalk Z I).2.2.2.1.mp hI
    have : Nontrivial (I.toModules.presheaf.stalk (genericPoint Z)) := hn
    have : Subsingleton
        (((TopCat.Presheaf.pushforward Ab i.base).obj I.toModules.presheaf).stalk
          (i.base (genericPoint Z))) := hzero
    have hz : Subsingleton (I.toModules.presheaf.stalk (genericPoint Z)) :=
      (hstalk.2.1 (genericPoint Z)).1.surjective.subsingleton
    exact not_subsingleton (α := I.toModules.presheaf.stalk (genericPoint Z)) hz
  have hclosure : closure ({i.base (genericPoint Z)} : Set X) = Set.range i.base := by
    simpa only [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq]
      using ((genericPoint_spec Z).image i.continuous).def
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hnot
    exact hx (hstalk.1 x hnot)
  · rw [← hclosure]
    exact hclosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hgeneric)

private theorem p_of_filtration {X : Scheme.{u}} [IsLocallyNoetherian X]
    (P : X.Modules → Prop) (hP_zero : P (0 : X.Modules))
    (hP_ext : ∀ (S : ShortComplex X.Modules), S.ShortExact →
      RingedSpace.IsCoherent X.toRingedSpace S.X₁ →
      RingedSpace.IsCoherent X.toRingedSpace S.X₂ →
      RingedSpace.IsCoherent X.toRingedSpace S.X₃ →
      P S.X₁ → P S.X₃ → P S.X₂)
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (m : ℕ) (c : Fin (m + 1) → Subobject F) (hc : Monotone c)
    (hbot : c 0 = ⊥) (htop : c (Fin.last m) = ⊤)
    (hcoh : ∀ j, RingedSpace.IsCoherent X.toRingedSpace (c j : X.Modules))
    (hpieces : ∀ j : Fin m,
      P (cokernel (Subobject.ofLE (c j.castSucc) (c j.succ)
        (hc j.castSucc_le_succ)))) : P F := by
  have hpc : ∀ j : Fin (m + 1), P (c j : X.Modules) := by
    intro j
    induction j using Fin.induction with
    | zero =>
      exact p_iso P hP_zero hP_ext
        (Subobject.isoOfEq _ _ hbot ≪≫ Subobject.botCoeIsoZero) (hcoh _) hP_zero
    | succ j ih =>
      let f := Subobject.ofLE (c j.castSucc) (c j.succ) (hc j.castSucc_le_succ)
      let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
      have hs : S.ShortExact := { exact := ShortComplex.exact_cokernel f }
      have hq := (((isCoherent_kernel_cokernel_biprod_and_submodule X).1
        (c j.castSucc) (c j.succ) (hcoh _) (hcoh _)).1 f).2
      exact hP_ext S hs (hcoh _) (hcoh _) hq ih (hpieces j)
  exact p_iso P hP_zero hP_ext
    (Subobject.isoOfEq _ _ htop ≪≫ asIso (⊤ : Subobject F).arrow).symm hF (hpc _)


set_option linter.unusedVariables false in
/-- A property satisfying extension, summand, and integral-support devissage hypotheses
holds for every coherent module on a Noetherian scheme.
Source: Stacks Project, Cohomology of Schemes, Lemma 01YM.
(blueprint: lem-weil-pbc-coherent-property-devissage-integral-subschemes)

Proof (the node's nine steps):

1. (Preliminaries.) (a) On the locally Noetherian $X$ an $\mathcal O_X$-module is coherent iff it
is quasi-coherent of finite type [pqf-lem-coherent-ft-locnoeth]; so $\mathcal O_X$ is coherent,
and kernels, cokernels and finite direct sums of maps of coherent modules, and quasi-coherent
submodules and quotients of a coherent module, are coherent
[lem-weil-pbc-coherent-kernel-cokernel-locnoeth](1),(2). The support of a coherent module is
closed [lem-weil-pbc-finite-type-module-support-closed]. (b) Stalks
[lem-weil-pbc-module-stalk-exact]: for a sub-$\mathcal O_X$-module $\mathcal F'\subseteq\mathcal
F$ the stalk $\mathcal F'_x\to\mathcal F_x$ is injective (1) and $(\mathcal F/\mathcal
F')_x=\mathcal F_x/\mathcal F'_x$ (3); hence $\operatorname{Supp}\mathcal
F'\subseteq\operatorname{Supp}\mathcal F$ and $\operatorname{Supp}(\mathcal F/\mathcal
F')\subseteq\operatorname{Supp}\mathcal F$, and $(\mathcal F/\mathcal F')_x=0$ iff $\mathcal
F'_x=\mathcal F_x$. The stalk of a finite direct sum is the direct sum of the stalks (filtered
colimits commute with finite direct sums). An $\mathcal O_X$-module, or an $\mathcal O_W$-module
on an open $W$, whose stalks are all $0$ is $0$, since its map to $0$ is bijective on stalks
[lem-weil-pbc-module-iso-on-stalks]. (c) Let $i:Z\to X$ be a closed immersion with $Z$ integral.
By definition [def-weil-closed-immersion] $i$ is a homeomorphism onto the closed subset $i(Z)$;
$Z$ is irreducible [def-pc-integral-scheme], so $i(Z)$ is an irreducible closed subset of $X$; if
$\eta$ is the generic point of $Z$ [lem-weil-pbc-scheme-sober], then $\xi=i(\eta)$ has closure
$i(Z)$ and is the only point of $X$ with this closure [lem-weil-pbc-scheme-sober]. $i$ is an
immersion, hence locally of finite type [lem-weil-pbc-immersion-base-change-lft](2), so $Z$ is
locally Noetherian [pqf-lem-locnoeth-lft]; thus $\mathcal O_Z$ is coherent and a sheaf of ideals
of $\mathcal O_Z$ is coherent iff it is quasi-coherent (by (a) on $Z$). For a quasi-coherent ideal
$\mathcal I\subseteq\mathcal O_Z$, $i_*\mathcal I$ is a coherent $\mathcal O_X$-module with
$\operatorname{Supp}(i_*\mathcal I)=i(\operatorname{Supp}\mathcal I)\subseteq i(Z)$
[lem-weil-pbc-closed-immersion-coherent-equivalence](1); and $(i_*\mathcal G)_{i(z)}\cong\mathcal
G_z$ naturally in the $\mathcal O_Z$-module $\mathcal G$
[lem-weil-pbc-closed-pushforward-stalks](2). Finally $i_*$ is computed sectionwise, $(i_*\mathcal
G)(V)=\mathcal G(i^{-1}V)$ [def-pc-module-pullback]: for quasi-coherent ideals $\mathcal
I_1\subseteq\mathcal I_2\subseteq\mathcal O_Z$ the induced map $i_*\mathcal I_1\to i_*\mathcal
I_2$ is injective on every open, and $i_*(\mathcal I^{\oplus r})=(i_*\mathcal I)^{\oplus r}$.

2. (Generic stalks of ideals.) Let $i:Z\to X$, $\eta$, $\xi$ be as in step 1(c) and $\mathcal
I\subseteq\mathcal O_Z$ a nonzero quasi-coherent ideal. By
[lem-weil-pbc-integral-scheme-ideal-generic-stalk], $\mathcal O_{Z,\eta}$ is a field, $\mathcal
I_\eta=\mathcal O_{Z,\eta}$ (as ideals, [lem-weil-pbc-ideal-module-product-stalk](1)), and
$\mathcal I(U)\ne0$ for every nonempty affine open $U\subseteq Z$. (a) $(i_*\mathcal
I)_\xi\cong\mathcal I_\eta\ne0$ (step 1(c)), so $\xi\in\operatorname{Supp}(i_*\mathcal I)$; this
support is closed and contained in $i(Z)=\overline{\{\xi\}}$ (step 1), hence
$\operatorname{Supp}(i_*\mathcal I)=i(Z)$. (b) If $\mathcal I'\subseteq\mathcal I$ is another
nonzero quasi-coherent ideal, then by the naturality in step 1(c) the stalk at $\xi$ of
$i_*\mathcal I'\to i_*\mathcal I$ is identified with the inclusion $\mathcal
I'_\eta\subseteq\mathcal I_\eta$, which is the identity of $\mathcal O_{Z,\eta}$; so it is
bijective, and so is its $r$-fold direct sum $(i_*\mathcal I')^{\oplus r}\to(i_*\mathcal
I)^{\oplus r}$ at $\xi$ (step 1(b)). (c) If $\mathcal I''\subseteq\mathcal O_Z$ is a further
nonzero quasi-coherent ideal, then $\mathcal I\cap\mathcal I''$ is a quasi-coherent ideal with
$(\mathcal I\cap\mathcal I'')(U)=\mathcal I(U)\cap\mathcal I''(U)$ for affine $U$
[lem-weil-pbc-quasi-coherent-ideal-intersection], and it is nonzero: for a nonempty affine open
$U$ ($Z\ne\emptyset$) pick $a\in\mathcal I(U)$, $b\in\mathcal I''(U)$ nonzero; $\mathcal O_Z(U)$
is a domain [def-pc-integral-scheme], so $0\ne ab\in\mathcal I(U)\cap\mathcal I''(U)$.

3. (Filtrations and isomorphisms.) (a) $\mathcal P$ is invariant under isomorphism: if
$\varphi:\mathcal F'\to\mathcal F$ is an isomorphism of coherent modules and $\mathcal P(\mathcal
F)$, then $0\to0\to\mathcal F'\xrightarrow{\varphi}\mathcal F\to0$ is a short exact sequence of
coherent modules whose outer terms have $\mathcal P$ by (0) and by assumption, so $\mathcal
P(\mathcal F')$ by (1). (b) If a coherent $\mathcal F$ has a chain $0=\mathcal
F_0\subseteq\dots\subseteq\mathcal F_m=\mathcal F$ of coherent submodules such that every
$\mathcal F_j/\mathcal F_{j-1}$ (coherent by [lem-weil-pbc-coherent-kernel-cokernel-locnoeth](1))
has $\mathcal P$, then $\mathcal P(\mathcal F)$: by induction on $j$, $\mathcal P(\mathcal F_0)$
is (0), and $\mathcal P(\mathcal F_{j-1})$, $\mathcal P(\mathcal F_j/\mathcal F_{j-1})$ and the
short exact sequence $0\to\mathcal F_{j-1}\to\mathcal F_j\to\mathcal F_j/\mathcal F_{j-1}\to0$
give $\mathcal P(\mathcal F_j)$ by (1).

4. Call an irreducible closed subset $T\subseteq X$ [def-weil-irreducible-components] *good* if
for every closed immersion $i:Z\to X$ with $Z$ integral and $i(Z)=T$ and every quasi-coherent
sheaf of ideals $\mathcal I\subseteq\mathcal O_Z$, $\mathcal P$ holds for $i_*\mathcal I$.
Suppose, for a contradiction, that the set $\mathcal S$ of irreducible closed subsets of $X$ that
are not good is nonempty. By [lem-weil-pbc-noetherian-scheme-closed-subsets-minimal] it has a
minimal element $T_0$; so every irreducible closed subset $T\subsetneq T_0$ is good. As $T_0$ is
not good, fix a closed immersion $i:Z_0\to X$ with $Z_0$ integral and $i(Z_0)=T_0$, and a
quasi-coherent ideal $\mathcal I_0\subseteq\mathcal O_{Z_0}$ such that $\mathcal P(i_*\mathcal
I_0)$ fails. Let $\eta$ be the generic point of $Z_0$ and $\xi=i(\eta)$, so
$\overline{\{\xi\}}=T_0$ (step 1(c)).

5. (Modules supported strictly inside $T_0$.) Claim: every coherent $\mathcal F$ with
$\operatorname{Supp}\mathcal F\subseteq T_0$ and $\xi\notin\operatorname{Supp}\mathcal F$ has
$\mathcal P$. If $\mathcal F=0$ this is (0). Otherwise take the chain $0=\mathcal
F_0\subseteq\dots\subseteq\mathcal F_m=\mathcal F$ of
[lem-weil-pbc-coherent-filtration-integral-subschemes], with $\mathcal F_j/\mathcal
F_{j-1}\cong(i_j)_*\mathcal I_j$, $i_j:Z_j\to X$ a closed immersion, $Z_j$ integral, $\mathcal
I_j\subseteq\mathcal O_{Z_j}$ a nonzero coherent, hence quasi-coherent (step 1(c)), ideal. By step
2(a), $\operatorname{Supp}((i_j)_*\mathcal I_j)=i_j(Z_j)$, and $\mathcal F_j/\mathcal F_{j-1}$ is
a quotient of a submodule of $\mathcal F$, so $i_j(Z_j)\subseteq\operatorname{Supp}\mathcal
F\subseteq T_0$ (step 1(b)); $i_j(Z_j)\ne T_0$ since $\xi\notin\operatorname{Supp}\mathcal F$. So
$i_j(Z_j)$ is an irreducible closed subset (step 1(c)) strictly contained in $T_0$, hence good
(step 4): $\mathcal P((i_j)_*\mathcal I_j)$, so $\mathcal P(\mathcal F_j/\mathcal F_{j-1})$ by
step 3(a), and $\mathcal P(\mathcal F)$ by step 3(b).

6. (The sheaf $\mathcal G$ and the map $\alpha$.) Apply hypothesis (3) to $i:Z_0\to X$ and $\xi$:
there is a coherent $\mathcal G$ with $\operatorname{Supp}\mathcal G=T_0$, $\mathfrak
m_\xi\mathcal G_\xi=0$ and property (3)(c). By
[lem-weil-pbc-coherent-generic-point-ideal-inclusion] there are $r\ge0$, a coherent (so
quasi-coherent, step 1(c)) ideal $\mathcal I\subseteq\mathcal O_{Z_0}$, an injective $\mathcal
O_X$-linear $\alpha:i_*(\mathcal I^{\oplus r})=(i_*\mathcal I)^{\oplus r}\to\mathcal G$ and an
open $W\ni\xi$ with $\alpha|_W$ an isomorphism; in particular $\alpha_\xi$ is bijective. Since
$\xi\in\operatorname{Supp}\mathcal G$, $0\ne\mathcal G_\xi\cong((i_*\mathcal I)_\xi)^{\oplus
r}\cong(\mathcal I_\eta)^{\oplus r}$ (step 1(b),(c)); hence $r\ge1$ and $\mathcal I\ne0$.

7. ($\mathcal P(i_*\mathcal I')$ for $0\ne\mathcal I'\subseteq\mathcal I$.) Let $\mathcal
I'\subseteq\mathcal I$ be a nonzero quasi-coherent ideal. Let $\beta:(i_*\mathcal I')^{\oplus
r}\to(i_*\mathcal I)^{\oplus r}\xrightarrow{\alpha}\mathcal G$; it is injective on every open
(step 1(c) and $\alpha$ injective), its source is coherent (step 1), and
$Q'=\operatorname{Coker}\beta$, with quotient map $c:\mathcal G\to Q'$, is coherent (step 1(a));
$\operatorname{Ker}c=\operatorname{Im}\beta$ and $\beta$ is an isomorphism of its source onto
$\operatorname{Im}\beta$. By step 2(b) and step 6, $\beta_\xi$ is bijective, so $Q'_\xi=0$; and
$\operatorname{Supp}Q'\subseteq\operatorname{Supp}\mathcal G=T_0$ (step 1(b)). Let $\mathcal
J=\operatorname{Ann}(Q')\subseteq\mathcal O_X$; by [lem-weil-pbc-scheme-theoretic-support](1),(4)
it is a quasi-coherent sheaf of ideals with $as=0$ for all local sections $a$ of $\mathcal J$ and
$s$ of $Q'$. $\mathcal J_\xi=\mathcal O_{X,\xi}$: $\operatorname{Supp}Q'$ is closed (step 1(a))
and misses $\xi$, so $W'=X\setminus\operatorname{Supp}Q'$ is an open neighbourhood of $\xi$ on
which all stalks of $Q'$ vanish, so $Q'|_{W'}=0$ (step 1(b)) and $1\in\operatorname{Ann}(Q')(W')$
by the definition of $\operatorname{Ann}$. Next $\mathcal J\mathcal
G\subseteq\operatorname{Im}\beta$: the composite $\mathcal J\otimes_{\mathcal O_X}\mathcal
G\to\mathcal G\xrightarrow{c}Q'$ sends each local section $a\otimes s$ to $a\,c(s)=0$; these
sections generate the tensor product sheaf locally [def-pur-sheaf-tensor-product], so the
composite is $0$ and its image $\mathcal J\mathcal G$ lies in
$\operatorname{Ker}c=\operatorname{Im}\beta$. By (3)(c) for $\mathcal J$ there is a coherent
$\mathcal G'\subseteq\mathcal J\mathcal G$ with $\mathcal G'_\xi=\mathcal G_\xi$ and $\mathcal
P(\mathcal G')$. Let $\mathcal G''=\beta^{-1}(\mathcal G')\subseteq(i_*\mathcal I')^{\oplus r}$;
$\beta$ maps it isomorphically onto $\mathcal G'$, so $\mathcal G''$ is coherent with $\mathcal
P(\mathcal G'')$ (step 3(a)), and $Q''=(i_*\mathcal I')^{\oplus r}/\mathcal G''$ is coherent (step
1(a)). As $\beta_\xi$ is bijective onto $\mathcal G_\xi=\mathcal G'_\xi$, $\mathcal G''_\xi$ is
the whole stalk and $Q''_\xi=0$; and
$\operatorname{Supp}Q''\subseteq\operatorname{Supp}(i_*\mathcal I')^{\oplus r}\subseteq T_0$ (step
1). By step 5, $\mathcal P(Q'')$. By (1) applied to $0\to\mathcal G''\to(i_*\mathcal I')^{\oplus
r}\to Q''\to0$, $\mathcal P((i_*\mathcal I')^{\oplus r})$, and by (2) ($r\ge1$, step 6), $\mathcal
P(i_*\mathcal I')$.

8. ($\mathcal P(i_*\mathcal I'')$ for every $\mathcal I''$; contradiction.) Let $\mathcal
I''\subseteq\mathcal O_{Z_0}$ be a quasi-coherent ideal. If $\mathcal I''=0$, then $i_*\mathcal
I''=0$ has $\mathcal P$ by (0). Otherwise $\mathcal I'=\mathcal I''\cap\mathcal I$ is a nonzero
quasi-coherent ideal (step 2(c); $\mathcal I\ne0$ by step 6) contained in $\mathcal I$, so
$\mathcal P(i_*\mathcal I')$ by step 7. The map $i_*\mathcal I'\to i_*\mathcal I''$ is injective
(step 1(c)); its cokernel $Q'''$ is coherent, $Q'''_\xi=0$ by step 2(b) (applied to $\mathcal
I'\subseteq\mathcal I''$) and step 1(b), and
$\operatorname{Supp}Q'''\subseteq\operatorname{Supp}(i_*\mathcal I'')\subseteq T_0$. So $\mathcal
P(Q''')$ by step 5 and $\mathcal P(i_*\mathcal I'')$ by (1). Taking $\mathcal I''=\mathcal I_0$
contradicts the choice of $\mathcal I_0$ in step 4. Hence $\mathcal S$ is empty: every irreducible
closed subset of $X$ is good.

9. (All coherent modules.) Let $\mathcal F$ be a coherent $\mathcal O_X$-module. If $\mathcal
F=0$, $\mathcal P(\mathcal F)$ is (0). Otherwise take the chain of
[lem-weil-pbc-coherent-filtration-integral-subschemes] with $\mathcal F_j/\mathcal
F_{j-1}\cong(i_j)_*\mathcal I_j$, $\mathcal I_j$ quasi-coherent (step 1(c)). Each $i_j(Z_j)$ is an
irreducible closed subset of $X$ (step 1(c)), good by step 8, so $\mathcal P((i_j)_*\mathcal I_j)$
and $\mathcal P(\mathcal F_j/\mathcal F_{j-1})$ (step 3(a)); by step 3(b), $\mathcal P(\mathcal
F)$. -/
theorem coherent_property_devissage_integral_subschemes
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (P : X.Modules → Prop)
    (hP_zero : P (0 : X.Modules))
    (hP_ext : ∀ (S : ShortComplex X.Modules), S.ShortExact →
      RingedSpace.IsCoherent X.toRingedSpace S.X₁ →
      RingedSpace.IsCoherent X.toRingedSpace S.X₂ →
      RingedSpace.IsCoherent X.toRingedSpace S.X₃ →
      P S.X₁ → P S.X₃ → P S.X₂)
    (hP_sum : ∀ (F : X.Modules) (r : ℕ),
      RingedSpace.IsCoherent X.toRingedSpace F → 1 ≤ r →
      P (@biproduct (Fin r) X.Modules _ _ (fun _ : Fin r ↦ F)
        (HasBiproduct.of_hasProduct (fun _ : Fin r ↦ F))) → P F)
    (hP_integral : ∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i]
      [IsIntegral Z] (ξ : X)
      (hclosure : closure ({ξ} : Set X) = Set.range i.base),
      ∃ G : X.Modules,
        RingedSpace.IsCoherent X.toRingedSpace G ∧
        ({x : X | ¬ Subsingleton (G.presheaf.stalk x)} = Set.range i.base) ∧
        (∀ g : X.presheaf.stalk ξ, ∀ m : (RingedSpace.moduleStalkFunctor
          X.toRingedSpace ξ).obj G, g ∈ IsLocalRing.maximalIdeal _ → g • m = 0) ∧
        ∀ (J : X.Modules) (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf)
          [Mono ι] [J.IsQuasicoherent],
          Function.Surjective
            ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map ι).hom →
          ∃ G' : Subobject G,
            RingedSpace.IsCoherent X.toRingedSpace (G' : X.Modules) ∧
            (∃ h : (G' : X.Modules) ⟶ idealModuleProduct ι G,
              G'.arrow = h ≫ idealModuleProductι ι G) ∧
            Function.Surjective ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map
              G'.arrow).hom ∧ P (G' : X.Modules)) :
    ∀ F : X.Modules, RingedSpace.IsCoherent X.toRingedSpace F → P F := by
  classical
  have : IsNoetherian X := {}
  have hgood : ∀ T : TopologicalSpace.Closeds X,
      ∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z],
        Set.range i.base ⊆ (T : Set X) →
          ∀ I : Z.IdealSheafData, P ((pushforward i).obj I.toModules) := by
    intro T
    induction T using WellFoundedLT.induction with
    | ind T ih =>
      intro Z i hi hZ hirange
      let ξ : X := i.base (genericPoint Z)
      have hclosure : closure ({ξ} : Set X) = Set.range i.base := by
        simpa only [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq]
          using ((genericPoint_spec Z).image i.continuous).def
      apply coherent_property_integral_ideals_of_small_support X P hP_zero hP_ext hP_sum
        Z i ξ hclosure
      · intro Q hQ hsupport hzero
        obtain ⟨m, c, hc, hbot, htop, hcoh, hquot⟩ :=
          exists_coherent_filtration_integral_subschemes X Q hQ
        apply p_of_filtration P hP_zero hP_ext Q hQ m c hc hbot htop hcoh
        intro k
        obtain ⟨Z', j, hj, hZ', I, hI, _, ⟨e⟩⟩ := hquot k
        have := hj
        have := hZ'
        let f := Subobject.ofLE (c k.castSucc) (c k.succ) (hc k.castSucc_le_succ)
        have hquotcoh := (((isCoherent_kernel_cokernel_biprod_and_submodule X).1
          (c k.castSucc) (c k.succ) (hcoh _) (hcoh _)).1 f).2
        have hpushcoh := coh_iso e hquotcoh
        have hrange := support_integral_ideal j I hI hpushcoh
        have hin : Set.range j.base ⊆
            {x : X | ¬ Subsingleton (Q.presheaf.stalk x)} := by
          rw [← hrange, ← support_iso e]
          exact (support_cokernel f).trans (support_mono (c k.succ).arrow)
        have hstrict : Set.range j.base ⊂ Set.range i.base := by
          refine ⟨hin.trans hsupport, ?_⟩
          intro hreverse
          exact hin (hreverse ⟨genericPoint Z, rfl⟩) hzero
        let T' : TopologicalSpace.Closeds X :=
          ⟨Set.range j.base, j.isClosedEmbedding.isClosed_range⟩
        have hlt : T' < T := Set.ssubset_of_ssubset_of_subset hstrict hirange
        exact p_iso P hP_zero hP_ext e hquotcoh (ih T' hlt Z' j (by rfl) I)
      · exact hP_integral Z i ξ hclosure
  intro F hF
  obtain ⟨m, c, hc, hbot, htop, hcoh, hquot⟩ :=
    exists_coherent_filtration_integral_subschemes X F hF
  have hpieces (j : Fin m) :
      P (cokernel (Subobject.ofLE (c j.castSucc) (c j.succ) (hc j.castSucc_le_succ))) := by
    obtain ⟨Z, i, hi, hZ, I, _, _, ⟨e⟩⟩ := hquot j
    have := hi
    have := hZ
    have hq := (((isCoherent_kernel_cokernel_biprod_and_submodule X).1
      (c j.castSucc) (c j.succ) (hcoh _) (hcoh _)).1
      (Subobject.ofLE (c j.castSucc) (c j.succ) (hc j.castSucc_le_succ))).2
    exact p_iso P hP_zero hP_ext e hq (hgood ⊤ Z i (by simp) I)
  exact p_of_filtration P hP_zero hP_ext F hF m c hc hbot htop hcoh hpieces

end AlgebraicGeometry.Scheme.Modules
