# The simply connected D₄ subgroup associated to a maximal torus in type F₄

`Langlands.GroupScheme.typeF4LongRootSubgroup` proves `Langlands.GroupScheme.TypeF4LongRootSubgroupStatement` in every universe.

Over the separable closure the given torus splits. Its absolute root datum has the Cartan type supplied by the Tits index of the ambient group. The long roots are detected by an asymmetric pair of Cartan integers, so their integral character span is Galois stable. The character anti-equivalence gives a group of multiplicative type mapping into the torus with that lattice as the kernel of character restriction.

The witness is the identity component of the centralizer of this toral image. It is connected reductive and contains the torus. Over the separable closure its roots are those ambient roots whose characters restrict trivially. The parity calculation identifies these with the long roots. For the common maximal torus the coroots agree with the ambient coroots. The four simple long coroots generate the full cocharacter lattice, giving semisimplicity and simple connectedness by the split criteria and field descent. The four simple long roots and their coroots give an actual base of type D₄. The rational root pairing is irreducible, giving absolute almost-simplicity, and comparison of bases transfers the D₄ numbering to an actual Tits index of the witness.

Platonov–Rapinchuk, *Algebraic Groups and Number Theory* (1994), §6.8, printed p. 371, identifies the long-root subgroup for the F₄ argument. The Lean proof uses a toral centralizer and its identity component.

## Source locators

- Platonov–Rapinchuk, `platonov-rapinchuk-1994-algebraic-groups-number-theory`, SHA-256 `c333b953ca0ace6306663f648cd853a75da55023bf873e0ef2688d997216717f`, §6.8, printed p. 371 and Theorem 2.6 C), printed p. 62.
- Brian Conrad, *Reductive group schemes* (2014), `conrad-2014-reductive-group-schemes`, SHA-256 `1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`, Remark 3.1.5 for the centralizer's identity component and Corollary 5.1.18 for irreducibility and absolute almost-simplicity.
