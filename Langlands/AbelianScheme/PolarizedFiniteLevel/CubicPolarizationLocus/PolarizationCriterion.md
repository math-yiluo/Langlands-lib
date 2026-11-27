# Geometric recognition of the divided Mumford map

`isPolarization_of_nsmul_mumford` uses `AlgebraicallyClosedFieldPolarizationDivisionStatement` to recognize a polarization from a positive multiple that is the Mumford map of a geometrically ample bundle. On each geometric fibre, additivity of base change and the dual comparison isomorphism identify the base change of the multiple with the multiple of the base-changed map. Applying the field statement then gives an ample Mumford presentation for the base-changed map itself.

The resulting geometric presentations give isogenies by `AmpleMumfordIsogeny.isIsogeny`. The isogeny properties descend from the algebraic closure to each residue field by fpqc descent, and `fiberwiseIsogeny` gives the relative isogeny. The presentation over the geometric field itself supplies the field-extension witness in the relative polarization predicate via the identity ring map.

The field input is the positive-multiple consequence of the characterization by symmetric maps and ample diagonal bundles in Edixhoven, van der Geer and Moonen, *Abelian Varieties*, preliminary draft (2012), (11.2), (11.4) and (11.5), printed pp. 159–160 (PDF pp. 163–164), source `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256 `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
