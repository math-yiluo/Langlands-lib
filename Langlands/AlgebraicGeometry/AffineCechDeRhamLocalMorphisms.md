# Section-ring pullbacks of local scheme lifts

For an open \(W\) of \(X\) and a morphism \(\gamma\colon W\to Y\) over
\(\operatorname{Spec}R\) mapping into an open \(T\) of \(Y\),
`pullbackSectionsFromOpen` is the section map
\(\Gamma(Y,T)\to\Gamma(W,W)\cong\Gamma(X,W)\), where \(\Gamma(W,W)\)
denotes the global sections of the open subscheme. The isomorphism between
sections on an open and global sections of the open subscheme identifies
the source coordinates, and the base equation makes the map an
\(R\)-algebra homomorphism.

Let \(r\colon Z\to X\) be surjective and \(m\colon Z\to Y\). Let affine
covers \(U\) of \(X\) and \(V\) of \(Y\) and an index map \(\beta\) satisfy
\(r^{-1}U_i\subseteq m^{-1}V_{\beta(i)}\). A local lift on a chart \(U_i\)
is a morphism \(\ell_i\colon U_i\to Y\) over \(\operatorname{Spec}R\)
whose restriction to \(r^{-1}U_i\) is \(m\). Restrict \(\ell_{\tau(i)}\) to
the intersection \(U_\tau\) of a tuple \(\tau\) containing \(\tau(i)\) as a
vertex. The restriction agrees with \(m\) on \(r^{-1}U_\tau\). Surjectivity
of \(r\) on points shows that it maps into the corresponding intersection
\(V_{\beta\tau}\) of target charts, so its pullback on sections is defined.

For separated \(X\) over \(\operatorname{Spec}R\), every tuple
intersection is affine. `LocalPullbacks.ofLocalMorphisms` collects these
section maps. It proves compatibility with restrictions by composing the
open inclusions and applying naturality of the section maps. Assume that for every affine open
\(W\) of \(X\) the section map of \(r\) has kernel \(I\,\Gamma(X,W)\). On
each affine intersection, the pullbacks from two vertices have the same
image under the section map of \(r\), namely the section map of \(m\).
Their difference therefore lies in the extended ideal.
`localMorphisms_congruent` gives the same conclusion for two families of
local lifts of \(m\). `localMorphisms_congruent_global` compares the local
lifts with the section maps of a global morphism \(\gamma\colon X\to Y\)
over \(\operatorname{Spec}R\) with \(\gamma\circ r=m\).

This construction gives the chart and overlap pullbacks used by Kai-Wen
Lan, *Arithmetic compactifications of PEL-type Shimura varieties*, revised
14 March 2021, Proposition 2.1.6.4, printed pp. 133–135. The retained source
is `lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.
