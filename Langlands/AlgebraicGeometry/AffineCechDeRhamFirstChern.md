# The first Chern cocycle of a line bundle in the affine Čech–de Rham complex

Let \(f\colon X\to\operatorname{Spec}R\) be a scheme over an affine base, let
\(U\) be a `Scheme.AffineOpenCover` of \(X\), with open images
\(U_i=\) `coverOpens U i`, and let \(L\) be an actual line bundle on \(X\),
an object of `Picard.LineBundle X`. For a tuple \(\sigma\) of indices write
\(U_\sigma\) for the intersection `inter (coverOpens U) σ` of the members
\(U_{\sigma(k)}\). The module defines the total degree-two cochain
`firstChernCocycle f U L e` of `AffineCechDeRham.C2` attached to
trivializations \(e\) of \(L\) on the members of \(U\), with components

\[
\bigl(0,\ (g_\sigma^{-1}\,dg_\sigma)_\sigma,\ 0\bigr)\in
C^{2,0}\oplus C^{1,1}\oplus C^{0,2},
\]

where \(g_\sigma\) is the actual transition unit of the trivializations on the
pair overlap \(U_\sigma=U_{\sigma(0)}\cap U_{\sigma(1)}\). It proves the Čech
and exterior closure equations of these components, the change of the cocycle
by a total boundary when the trivializations change, and its compatibility
with restriction to an affine refinement, and it specializes the construction
to the Poincaré line bundle.

None of these constructions uses smoothness or separatedness of \(f\), or
finiteness of the cover. When \(f\) is smooth and separated and the cover is
finite, these are the cochains of the complex whose first cohomology is
`AffineCechDeRham.H1`; the Library's total complex stops at `D1`, so the
closure equations are stated componentwise.

## Trivializations as frames

`LocalFrame L V` is a trivialization of \(L\) on an open \(V\), recorded as a
frame: a section \(e\in\Gamma(V,L)\) such that for every open \(W\subseteq V\)
the map \(\Gamma(W,\mathcal O_X)\to\Gamma(W,L)\), \(a\mapsto a\,e|_W\), is
bijective. Thus a frame gives, on every open \(W\subseteq V\), a
\(\Gamma(W,\mathcal O_X)\)-linear bijection from functions to sections of
\(L\), compatible with restriction; the module constructs frames from
trivializing isomorphisms (`LocalFrame.ofIso` below) and does not construct the
converse isomorphism from a frame. `restrictFrame` is the
restricted section \(e|_W\), `coord` the inverse bijection (the coordinate of a
section in the frame), with `coord_smul` and `coord_eq`, and
`LocalFrame.restrict` restricts a frame to a smaller open.

`LocalFrame.ofIso` takes an isomorphism
\(\tau\colon L|_V\cong\mathcal O_V\), in the form
`L.obj.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf` of
`LineBundle.localTrivialization`, to the frame \(\tau^{-1}(1)\). It uses the
chart coordinates `SectionClearing.chartE` and their inverse `chartF` of the
module `Modules.LineBundleSectionClearingProof`: the frame is
`chartF τ V le_rfl 1`, and since `chartE` is linear over functions, commutes
with restriction and is inverse to `chartF`, it sends \(a\,e|_W\) to \(a\).
Hence \(a\mapsto a\,e|_W\) is bijective with inverse `chartE τ W`, and
`ofIso_coord` identifies the frame coordinates with the chart coordinates of
\(\tau\). The abbreviation `structureIso` only retypes \(\tau\) with target
`structureSheaf`, the name used by those chart lemmas for the same unit sheaf.

## Transition units and the sign convention

For frames \(e_1\) on \(V_1\) and \(e_2\) on \(V_2\) and an open
\(W\subseteq V_1\cap V_2\), `LocalFrame.transition e₁ e₂` is the unit
\(g\in\Gamma(W,\mathcal O_X)^\times\) with

\[
e_2|_W=g\,e_1|_W
\]

(`transition_smul`, uniqueness `transition_val_eq`). Its value is the
coordinate of \(e_2|_W\) in \(e_1\) and its inverse the coordinate of
\(e_1|_W\) in \(e_2\); the two products are \(1\) by injectivity of
\(a\mapsto a\,e_i|_W\). The lemmas `transition_self`, `transition_mul`
(\(g_{12}g_{23}=g_{13}\) for three frames), `transition_inv`,
`map_transition` (restricting the unit to \(W'\subseteq W\) gives the
transition unit on \(W'\), by `Scheme.Modules.map_smul`) and
`transition_restrict` (restricted frames have the restricted transition unit)
follow from uniqueness.

A `CoverTrivialization U L` is a frame on every \(U_i\);
`CoverTrivialization.ofIsos` makes one from trivializing isomorphisms
\(\tau_i\colon L|_{U_i}\cong\mathcal O_{U_i}\). For a tuple \(\tau\) and
vertices \(a,b\), `tupleTransition e e' τ a b` is the transition unit on
\(U_\tau\) from the frame of \(e\) at \(\tau(a)\) to the frame of \(e'\) at
\(\tau(b)\); `tupleTransition_mul`, `tupleTransition_inv` and
`map_tupleTransition` (restriction from the intersection of a subtuple
\(\tau\circ\theta\) to \(U_\tau\)) are the corresponding identities.

The transition unit of the cocycle is `transitionUnit e σ`
\(=g_\sigma\) on \(U_\sigma\), defined by

\[
e_{\sigma(1)}=g_\sigma\,e_{\sigma(0)}\qquad\text{on }U_\sigma .
\]

For frames \(e_i=\tau_i^{-1}(1)\) of isomorphisms this is
\(g_\sigma=\tau_{\sigma(0)}\bigl(\tau_{\sigma(1)}^{-1}(1)\bigr)\), so
multiplication by \(g_{ij}\) is \(\tau_i\circ\tau_j^{-1}\) on \(U_i\cap U_j\)
(`transitionUnit_ofIsos`). The Library's Čech differential `cechD` is the
alternating sum of face restrictions, \((\partial h)_{ij}=h_j-h_i\) and
\((\partial\omega)_{ijk}=\omega_{jk}-\omega_{ik}+\omega_{ij}\). With the
orientation above, \((g_{ij})\) is a multiplicative Čech cocycle in the same
face convention, and rescaling the frames changes it by the multiplicative
Čech coboundary of the rescaling units in that convention, so that the
first Chern cocycle changes by \(+D_1\) of their logarithmic differentials
(see below). `transitionUnit_const` gives \(g_{ii}=1\), and
`transitionUnit_cocycle` gives, after restriction to \(U_{ijk}\),

\[
g_{ij}\,g_{jk}=g_{ik},\qquad\text{that is}\qquad
g_{jk}\,g_{ik}^{-1}\,g_{ij}=1 ,
\]

the three factors being restricted from the faces omitting the vertices
\(2\), \(0\) and \(1\). For a second cover trivialization \(e'\), let
\(u_i\) be the unit on \(U_i\) with \(e'_i=u_i\,e_i\). On an intersection
\(U_\tau\), `tupleTransition e e' τ a a` is the restriction of
\(u_{\tau(a)}\) (`map_chartChange` restricts it from the one-vertex
intersection at \(\tau(a)\)). The units change by the multiplicative Čech
coboundary of \(u\) in this convention, \(g'_{ij}=u_i^{-1}\,g_{ij}\,u_j\)
(`transitionUnit_change`).

## Logarithmic differentials

`RelativeForms.dlog u` is \(u^{-1}\,du\in\Omega^1_{A/R}\) for a unit \(u\) of an
\(R\)-algebra \(A\). The Leibniz rule gives `dlog_mul`
(\(d\log(uv)=d\log u+d\log v\)), hence `dlog_one` and `dlog_inv`;
`mapOne_dlog` is naturality under algebra homomorphisms, by semilinearity of
`mapOne` and `mapOne_d`. For `dOne_dlog`, the formula
\(d(a\,db)=da\wedge db\) of `dOne_smul_d` gives
\(d(u^{-1}du)=d(u^{-1})\wedge du\); by
`Derivation.leibniz_of_mul_eq_one`, \(d(u^{-1})=-u^{-2}\,du\), and
\(du\wedge du=0\) because the exterior square is alternating.

On the section rings, `sectionUnit` views a unit of \(\Gamma(W,\mathcal O_X)\)
as a unit of the section algebra `sectionAlgebras f` on \(W\) (the same ring),
and `dlogSection f g` is \(g^{-1}dg\) in `oneForms f` on \(W\).
`oneForms_map_dlogSection` says that restriction of one-forms sends
\(g^{-1}dg\) to \(\rho(g)^{-1}d\rho(g)\) for the restricted unit \(\rho(g)\);
`exteriorD1_dlogSection`, `dlogSection_mul` and `dlogSection_inv` are the
other identities on sections.

## The cocycle and its closure equations

`firstChernCocycle f U L e` is
`(0, fun σ => dlogSection f (transitionUnit e σ), 0)`: zero in the Čech
2-cochains of functions, \(\omega_\sigma=g_\sigma^{-1}dg_\sigma\) in the Čech
1-cochains of relative one-forms on the pair overlaps, and zero in the chart
two-forms. The lemmas `firstChernCocycle_fst`, `firstChernCocycle_snd_fst`
and `firstChernCocycle_snd_snd` record the components.

Extending the rule \(\partial\oplus(-1)^p d\) of `D0` and `D1` to total degree
two, an element \((c,\omega,\eta)\) of \(C^2\) has total differential with
components \(\partial c\), \(\partial\omega+dc\), \(\partial\eta-d\omega\) and
\(d\eta\). For \((0,\omega,0)\) the conditions are \(\partial\omega=0\) and
\(d\omega=0\), and the module proves both:

- `cechD_firstChernCocycle`: \(\partial\omega=0\) in the Čech 2-cochains of
  one-forms. On a triple \(\tau\), after `oneForms_map_dlogSection` and
  `map_tupleTransition`, the alternating sum is
  \(d\log g_{12}-d\log g_{02}+d\log g_{01}\) on \(U_\tau\), which vanishes by
  \(g_{01}g_{12}=g_{02}\) and `dlogSection_mul`.
- `exteriorD1_firstChernCocycle`: \(d\omega=0\) on every pair overlap, by
  `exteriorD1_dlogSection`.

## Changing the trivializations

For two cover trivializations \(e,e'\) of \(L\) on the same cover, with
\(e'_i=u_i\,e_i\), `frameChangeCochain f e e'` is the degree-one cochain
\((0,(u_i^{-1}du_i)_i)\in C^{1,0}\oplus C^{0,1}\). Its total differential is
\(D_1(0,b)=(0,\partial b,db)\), and `firstChernCocycle_change` proves

\[
\mathrm{c}(e')=\mathrm{c}(e)+D_1\bigl(0,(u_i^{-1}du_i)_i\bigr).
\]

In the one-form component, \(g'_{ij}=u_i^{-1}g_{ij}u_j\) gives
\(d\log g'_{ij}=d\log g_{ij}+d\log u_j-d\log u_i\), and
\(d\log u_j-d\log u_i=(\partial b)_{ij}\) with the face convention of
`cechD`; the other components are \(0=\partial 0\) and
\(0=d(u_i^{-1}du_i)\). `firstChernCocycle_sub_mem_range_D1` states the
consequence that the difference lies in the range of `D1`.

## Restriction to an affine refinement

Let \(V\) be another affine open cover of \(X\) with an index map \(\beta\)
such that \(V_k\subseteq U_{\beta(k)}\). Then \(V_\sigma\subseteq
U_{\beta\circ\sigma}\) (`inter_le_refine`). `refineCochains` restricts a
Čech cochain \(c\) for \(U\) to the cochain \(\sigma\mapsto
c_{\beta\circ\sigma}|_{V_\sigma}\) for \(V\), and `refineC2` does this on the
three components of \(C^2\). `CoverTrivialization.restrictRefinement`
restricts the frame on \(U_{\beta(k)}\) to \(V_k\).
`firstChernCocycle_restrictRefinement` proves that the cocycle of the
restricted frames is the restriction of the cocycle: by `transition_restrict`
and `map_transition`, the transition unit of the restricted frames on
\(V_\sigma\) is the restriction of \(g_{\beta\circ\sigma}\), and
`oneForms_map_dlogSection` moves the restriction through \(d\log\).

## The Poincaré line bundle

For an abelian scheme \(A\) over \(S=\operatorname{Spec}R\) and a proof
`hA : HasDualScheme A`, `poincareStructureMorphism A hA` is the structure
morphism of the total space `((baseChange (dualScheme A hA).hom).obj A).X.left`
of \(A\times_S A^\vee\) to \(S\), through the dual scheme.
For an affine open cover of this total space and frames of
`poincareLineBundle A hA` on its members, `poincareFirstChernCocycle A hA U e`
is `firstChernCocycle` of the actual Poincaré line bundle, and
`poincareFirstChernCocycle_closed` records its two closure equations. The
change-of-frames and refinement theorems apply to it without change. The
module supplies no cover; the trivializing affine cover is part of the input.

## Source correspondence

Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura varieties*,
revised 14 March 2021, in the discussion before Corollary 2.2.4.8 on printed
p. 156 (PDF p. 184), says that, as in Deligne–Pappas (Compositio Math. 90,
1994), 1.5, the first Chern class of the Poincaré invertible sheaf on
\(A\times_S A^\vee\) induces an alternating pairing between
\(H_1^{\mathrm{dR}}(A/S)\) and \(H_1^{\mathrm{dR}}(A^\vee/S)\), from which the
pairing \(\langle\cdot,\cdot\rangle_\lambda\) of a polarization is defined; the
passage gives no explicit cocycle. The total complex and its
sign rule \(\partial\oplus(-1)^p d\) are those of §2.1.6, printed pp. 129–132
(PDF pp. 157–160), as implemented in `AffineCechDeRham`.

The cocycle is derived from the standard construction of the de Rham first
Chern class: mathematically, the class of \(L\) in
\(\check H^1(U,\mathcal O_X^\times)\) is represented by the transition units, the logarithmic differential
\(d\log\colon\mathcal O_X^\times\to\Omega^1_{X/S}\) lands in closed forms, and
a Čech 1-cocycle of closed one-forms \(\omega\) gives the total 2-cocycle
\((0,\omega,0)\) through the inclusion of the truncation in form degrees at
least one. The orientation \(e_j=g_{ij}e_i\), equivalently
\(g_{ij}=\tau_i\tau_j^{-1}\), is chosen as explained above so that \((g_{ij})\)
is a multiplicative cocycle for the face convention of `cechD` and a change of
frames changes the cocycle by \(+D_1\) of the logarithmic differentials of
the rescaling units. The module does not construct the class in
\(\check H^1(U,\mathcal O_X^\times)\) or a degree-two cohomology group. The retained
source is `lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.
[Revised dissertation](https://www.kwlan.org/articles/cpt-PEL-type-thesis-revision.pdf)
